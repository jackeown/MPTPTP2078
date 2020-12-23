%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JvLFMo7rQ8

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 362 expanded)
%              Number of leaves         :   26 ( 118 expanded)
%              Depth                    :   19
%              Number of atoms          :  747 (5740 expanded)
%              Number of equality atoms :   43 ( 323 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relset_1_type,type,(
    k6_relset_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t41_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ A @ B )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( r2_hidden @ C @ A )
          & ( r2_hidden @ ( k1_funct_1 @ E @ C ) @ D ) )
       => ( ( B = k1_xboole_0 )
          | ( ( k1_funct_1 @ ( k6_relset_1 @ A @ B @ D @ E ) @ C )
            = ( k1_funct_1 @ E @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( ( v1_funct_1 @ E )
          & ( v1_funct_2 @ E @ A @ B )
          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( r2_hidden @ C @ A )
            & ( r2_hidden @ ( k1_funct_1 @ E @ C ) @ D ) )
         => ( ( B = k1_xboole_0 )
            | ( ( k1_funct_1 @ ( k6_relset_1 @ A @ B @ D @ E ) @ C )
              = ( k1_funct_1 @ E @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_funct_2])).

thf('0',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_E @ sk_C ) @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_E @ sk_C ) @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k1_relat_1 @ X5 ) )
      | ( X6 = k1_xboole_0 )
      | ( X6
       != ( k1_funct_1 @ X5 @ X4 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( ( k1_funct_1 @ X5 @ X4 )
        = k1_xboole_0 )
      | ( r2_hidden @ X4 @ ( k1_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t86_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X11 @ X10 ) @ X12 )
      | ( r2_hidden @ X10 @ ( k1_relat_1 @ ( k8_relat_1 @ X12 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t86_funct_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k8_relat_1 @ X2 @ X0 ) ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k8_relat_1 @ X2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( ( k1_funct_1 @ sk_E @ sk_C )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E )
    | ( r2_hidden @ sk_C @ ( k1_relat_1 @ ( k8_relat_1 @ sk_D @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('13',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k1_funct_1 @ sk_E @ sk_C )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_C @ ( k1_relat_1 @ ( k8_relat_1 @ sk_D @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['7','8','13'])).

thf(t87_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) )
       => ( ( k1_funct_1 @ ( k8_relat_1 @ B @ C ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ ( k8_relat_1 @ X14 @ X15 ) ) )
      | ( ( k1_funct_1 @ ( k8_relat_1 @ X14 @ X15 ) @ X13 )
        = ( k1_funct_1 @ X15 @ X13 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t87_funct_1])).

thf('16',plain,
    ( ( ( k1_funct_1 @ sk_E @ sk_C )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_funct_1 @ ( k8_relat_1 @ sk_D @ sk_E ) @ sk_C )
      = ( k1_funct_1 @ sk_E @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['11','12'])).

thf('18',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k1_funct_1 @ sk_E @ sk_C )
      = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k8_relat_1 @ sk_D @ sk_E ) @ sk_C )
      = ( k1_funct_1 @ sk_E @ sk_C ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ( k1_funct_1 @ ( k6_relset_1 @ sk_A @ sk_B @ sk_D @ sk_E ) @ sk_C )
 != ( k1_funct_1 @ sk_E @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k6_relset_1 @ A @ B @ C @ D )
        = ( k8_relat_1 @ C @ D ) ) ) )).

thf('22',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( ( k6_relset_1 @ X18 @ X19 @ X16 @ X17 )
        = ( k8_relat_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_relset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k6_relset_1 @ sk_A @ sk_B @ X0 @ sk_E )
      = ( k8_relat_1 @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ( k1_funct_1 @ ( k8_relat_1 @ sk_D @ sk_E ) @ sk_C )
 != ( k1_funct_1 @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,
    ( ( k1_funct_1 @ sk_E @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['19','24'])).

thf('26',plain,(
    r2_hidden @ k1_xboole_0 @ sk_D ),
    inference(demod,[status(thm)],['0','25'])).

thf(fc9_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k8_relat_1 @ A @ B ) ) ) ) )).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_funct_1 @ ( k8_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc9_funct_1])).

thf('29',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ( ( k1_funct_1 @ X5 @ X4 )
        = k1_xboole_0 )
      | ( r2_hidden @ X4 @ ( k1_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('30',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ ( k8_relat_1 @ X12 @ X11 ) ) )
      | ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t86_funct_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
        = k1_xboole_0 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ( k1_funct_1 @ ( k8_relat_1 @ sk_D @ sk_E ) @ sk_C )
 != ( k1_funct_1 @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('37',plain,
    ( ( k1_funct_1 @ sk_E @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['19','24'])).

thf('38',plain,(
    ( k1_funct_1 @ ( k8_relat_1 @ sk_D @ sk_E ) @ sk_C )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ( r2_hidden @ sk_C @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['11','12'])).

thf('41',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ sk_C @ ( k1_relat_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    r2_hidden @ sk_C @ ( k1_relat_1 @ sk_E ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X11 @ X10 ) @ X12 )
      | ( r2_hidden @ X10 @ ( k1_relat_1 @ ( k8_relat_1 @ X12 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t86_funct_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_funct_1 @ sk_E )
      | ( r2_hidden @ sk_C @ ( k1_relat_1 @ ( k8_relat_1 @ X0 @ sk_E ) ) )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_E @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['11','12'])).

thf('47',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k1_funct_1 @ sk_E @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['19','24'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_C @ ( k1_relat_1 @ ( k8_relat_1 @ X0 @ sk_E ) ) )
      | ~ ( r2_hidden @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('50',plain,(
    r2_hidden @ sk_C @ ( k1_relat_1 @ ( k8_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['26','49'])).

thf('51',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ ( k8_relat_1 @ X14 @ X15 ) ) )
      | ( ( k1_funct_1 @ ( k8_relat_1 @ X14 @ X15 ) @ X13 )
        = ( k1_funct_1 @ X15 @ X13 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t87_funct_1])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_funct_1 @ ( k8_relat_1 @ sk_D @ sk_E ) @ sk_C )
      = ( k1_funct_1 @ sk_E @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['11','12'])).

thf('54',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k1_funct_1 @ sk_E @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['19','24'])).

thf('56',plain,
    ( ( k1_funct_1 @ ( k8_relat_1 @ sk_D @ sk_E ) @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,(
    ( k1_funct_1 @ ( k8_relat_1 @ sk_D @ sk_E ) @ sk_C )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['36','37'])).

thf('58',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['56','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JvLFMo7rQ8
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:04:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 45 iterations in 0.042s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(k6_relset_1_type, type, k6_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.50  thf(t41_funct_2, conjecture,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.50     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.20/0.50         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.50       ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ ( k1_funct_1 @ E @ C ) @ D ) ) =>
% 0.20/0.50         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.50           ( ( k1_funct_1 @ ( k6_relset_1 @ A @ B @ D @ E ) @ C ) =
% 0.20/0.50             ( k1_funct_1 @ E @ C ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.50        ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.20/0.50            ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.50          ( ( ( r2_hidden @ C @ A ) & 
% 0.20/0.50              ( r2_hidden @ ( k1_funct_1 @ E @ C ) @ D ) ) =>
% 0.20/0.50            ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.50              ( ( k1_funct_1 @ ( k6_relset_1 @ A @ B @ D @ E ) @ C ) =
% 0.20/0.50                ( k1_funct_1 @ E @ C ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t41_funct_2])).
% 0.20/0.50  thf('0', plain, ((r2_hidden @ (k1_funct_1 @ sk_E @ sk_C) @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain, ((r2_hidden @ (k1_funct_1 @ sk_E @ sk_C) @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d4_funct_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.50       ( ![B:$i,C:$i]:
% 0.20/0.50         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.20/0.50             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.20/0.50               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.50           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.20/0.50             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.20/0.50               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         ((r2_hidden @ X4 @ (k1_relat_1 @ X5))
% 0.20/0.50          | ((X6) = (k1_xboole_0))
% 0.20/0.50          | ((X6) != (k1_funct_1 @ X5 @ X4))
% 0.20/0.50          | ~ (v1_funct_1 @ X5)
% 0.20/0.50          | ~ (v1_relat_1 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X5)
% 0.20/0.50          | ~ (v1_funct_1 @ X5)
% 0.20/0.50          | ((k1_funct_1 @ X5 @ X4) = (k1_xboole_0))
% 0.20/0.50          | (r2_hidden @ X4 @ (k1_relat_1 @ X5)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.50  thf(t86_funct_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.50       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) ) <=>
% 0.20/0.50         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.50           ( r2_hidden @ ( k1_funct_1 @ C @ A ) @ B ) ) ) ))).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X10 @ (k1_relat_1 @ X11))
% 0.20/0.50          | ~ (r2_hidden @ (k1_funct_1 @ X11 @ X10) @ X12)
% 0.20/0.50          | (r2_hidden @ X10 @ (k1_relat_1 @ (k8_relat_1 @ X12 @ X11)))
% 0.20/0.50          | ~ (v1_funct_1 @ X11)
% 0.20/0.50          | ~ (v1_relat_1 @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [t86_funct_1])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (((k1_funct_1 @ X0 @ X1) = (k1_xboole_0))
% 0.20/0.50          | ~ (v1_funct_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_funct_1 @ X0)
% 0.20/0.50          | (r2_hidden @ X1 @ (k1_relat_1 @ (k8_relat_1 @ X2 @ X0)))
% 0.20/0.50          | ~ (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ X2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (r2_hidden @ (k1_funct_1 @ X0 @ X1) @ X2)
% 0.20/0.50          | (r2_hidden @ X1 @ (k1_relat_1 @ (k8_relat_1 @ X2 @ X0)))
% 0.20/0.50          | ~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_funct_1 @ X0)
% 0.20/0.50          | ((k1_funct_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      ((((k1_funct_1 @ sk_E @ sk_C) = (k1_xboole_0))
% 0.20/0.50        | ~ (v1_funct_1 @ sk_E)
% 0.20/0.50        | ~ (v1_relat_1 @ sk_E)
% 0.20/0.50        | (r2_hidden @ sk_C @ (k1_relat_1 @ (k8_relat_1 @ sk_D @ sk_E))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '6'])).
% 0.20/0.50  thf('8', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc2_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.50          | (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_E))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf(fc6_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.50  thf('13', plain, ((v1_relat_1 @ sk_E)),
% 0.20/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      ((((k1_funct_1 @ sk_E @ sk_C) = (k1_xboole_0))
% 0.20/0.50        | (r2_hidden @ sk_C @ (k1_relat_1 @ (k8_relat_1 @ sk_D @ sk_E))))),
% 0.20/0.50      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.20/0.50  thf(t87_funct_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.50       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k8_relat_1 @ B @ C ) ) ) =>
% 0.20/0.50         ( ( k1_funct_1 @ ( k8_relat_1 @ B @ C ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X13 @ (k1_relat_1 @ (k8_relat_1 @ X14 @ X15)))
% 0.20/0.50          | ((k1_funct_1 @ (k8_relat_1 @ X14 @ X15) @ X13)
% 0.20/0.50              = (k1_funct_1 @ X15 @ X13))
% 0.20/0.50          | ~ (v1_funct_1 @ X15)
% 0.20/0.50          | ~ (v1_relat_1 @ X15))),
% 0.20/0.50      inference('cnf', [status(esa)], [t87_funct_1])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      ((((k1_funct_1 @ sk_E @ sk_C) = (k1_xboole_0))
% 0.20/0.50        | ~ (v1_relat_1 @ sk_E)
% 0.20/0.50        | ~ (v1_funct_1 @ sk_E)
% 0.20/0.50        | ((k1_funct_1 @ (k8_relat_1 @ sk_D @ sk_E) @ sk_C)
% 0.20/0.50            = (k1_funct_1 @ sk_E @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf('17', plain, ((v1_relat_1 @ sk_E)),
% 0.20/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('18', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      ((((k1_funct_1 @ sk_E @ sk_C) = (k1_xboole_0))
% 0.20/0.50        | ((k1_funct_1 @ (k8_relat_1 @ sk_D @ sk_E) @ sk_C)
% 0.20/0.50            = (k1_funct_1 @ sk_E @ sk_C)))),
% 0.20/0.50      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (((k1_funct_1 @ (k6_relset_1 @ sk_A @ sk_B @ sk_D @ sk_E) @ sk_C)
% 0.20/0.50         != (k1_funct_1 @ sk_E @ sk_C))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(redefinition_k6_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( ( k6_relset_1 @ A @ B @ C @ D ) = ( k8_relat_1 @ C @ D ) ) ))).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.50         (((k6_relset_1 @ X18 @ X19 @ X16 @ X17) = (k8_relat_1 @ X16 @ X17))
% 0.20/0.50          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.20/0.50      inference('cnf', [status(esa)], [redefinition_k6_relset_1])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((k6_relset_1 @ sk_A @ sk_B @ X0 @ sk_E) = (k8_relat_1 @ X0 @ sk_E))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (((k1_funct_1 @ (k8_relat_1 @ sk_D @ sk_E) @ sk_C)
% 0.20/0.50         != (k1_funct_1 @ sk_E @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['20', '23'])).
% 0.20/0.50  thf('25', plain, (((k1_funct_1 @ sk_E @ sk_C) = (k1_xboole_0))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['19', '24'])).
% 0.20/0.50  thf('26', plain, ((r2_hidden @ k1_xboole_0 @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['0', '25'])).
% 0.20/0.50  thf(fc9_funct_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.50       ( ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) & 
% 0.20/0.50         ( v1_funct_1 @ ( k8_relat_1 @ A @ B ) ) ) ))).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]:
% 0.20/0.50         ((v1_relat_1 @ (k8_relat_1 @ X8 @ X9))
% 0.20/0.50          | ~ (v1_funct_1 @ X9)
% 0.20/0.50          | ~ (v1_relat_1 @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc9_funct_1])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i]:
% 0.20/0.50         ((v1_funct_1 @ (k8_relat_1 @ X8 @ X9))
% 0.20/0.50          | ~ (v1_funct_1 @ X9)
% 0.20/0.50          | ~ (v1_relat_1 @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc9_funct_1])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X5)
% 0.20/0.50          | ~ (v1_funct_1 @ X5)
% 0.20/0.50          | ((k1_funct_1 @ X5 @ X4) = (k1_xboole_0))
% 0.20/0.50          | (r2_hidden @ X4 @ (k1_relat_1 @ X5)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X10 @ (k1_relat_1 @ (k8_relat_1 @ X12 @ X11)))
% 0.20/0.50          | (r2_hidden @ X10 @ (k1_relat_1 @ X11))
% 0.20/0.50          | ~ (v1_funct_1 @ X11)
% 0.20/0.50          | ~ (v1_relat_1 @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [t86_funct_1])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (((k1_funct_1 @ (k8_relat_1 @ X1 @ X0) @ X2) = (k1_xboole_0))
% 0.20/0.50          | ~ (v1_funct_1 @ (k8_relat_1 @ X1 @ X0))
% 0.20/0.50          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.20/0.50          | ~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_funct_1 @ X0)
% 0.20/0.50          | (r2_hidden @ X2 @ (k1_relat_1 @ X0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_funct_1 @ X0)
% 0.20/0.50          | (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.20/0.50          | ~ (v1_funct_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.20/0.50          | ((k1_funct_1 @ (k8_relat_1 @ X1 @ X0) @ X2) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['28', '31'])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (((k1_funct_1 @ (k8_relat_1 @ X1 @ X0) @ X2) = (k1_xboole_0))
% 0.20/0.50          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.20/0.50          | (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.20/0.50          | ~ (v1_funct_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_funct_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ X0)
% 0.20/0.50          | ~ (v1_funct_1 @ X0)
% 0.20/0.50          | (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.20/0.50          | ((k1_funct_1 @ (k8_relat_1 @ X1 @ X0) @ X2) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['27', '33'])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (((k1_funct_1 @ (k8_relat_1 @ X1 @ X0) @ X2) = (k1_xboole_0))
% 0.20/0.50          | (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.20/0.50          | ~ (v1_funct_1 @ X0)
% 0.20/0.50          | ~ (v1_relat_1 @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (((k1_funct_1 @ (k8_relat_1 @ sk_D @ sk_E) @ sk_C)
% 0.20/0.50         != (k1_funct_1 @ sk_E @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['20', '23'])).
% 0.20/0.50  thf('37', plain, (((k1_funct_1 @ sk_E @ sk_C) = (k1_xboole_0))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['19', '24'])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (((k1_funct_1 @ (k8_relat_1 @ sk_D @ sk_E) @ sk_C) != (k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.50        | ~ (v1_relat_1 @ sk_E)
% 0.20/0.50        | ~ (v1_funct_1 @ sk_E)
% 0.20/0.50        | (r2_hidden @ sk_C @ (k1_relat_1 @ sk_E)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['35', '38'])).
% 0.20/0.50  thf('40', plain, ((v1_relat_1 @ sk_E)),
% 0.20/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('41', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.50        | (r2_hidden @ sk_C @ (k1_relat_1 @ sk_E)))),
% 0.20/0.50      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.20/0.50  thf('43', plain, ((r2_hidden @ sk_C @ (k1_relat_1 @ sk_E))),
% 0.20/0.50      inference('simplify', [status(thm)], ['42'])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X10 @ (k1_relat_1 @ X11))
% 0.20/0.50          | ~ (r2_hidden @ (k1_funct_1 @ X11 @ X10) @ X12)
% 0.20/0.50          | (r2_hidden @ X10 @ (k1_relat_1 @ (k8_relat_1 @ X12 @ X11)))
% 0.20/0.50          | ~ (v1_funct_1 @ X11)
% 0.20/0.50          | ~ (v1_relat_1 @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [t86_funct_1])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ sk_E)
% 0.20/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.50          | (r2_hidden @ sk_C @ (k1_relat_1 @ (k8_relat_1 @ X0 @ sk_E)))
% 0.20/0.50          | ~ (r2_hidden @ (k1_funct_1 @ sk_E @ sk_C) @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.50  thf('46', plain, ((v1_relat_1 @ sk_E)),
% 0.20/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('47', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('48', plain, (((k1_funct_1 @ sk_E @ sk_C) = (k1_xboole_0))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['19', '24'])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r2_hidden @ sk_C @ (k1_relat_1 @ (k8_relat_1 @ X0 @ sk_E)))
% 0.20/0.50          | ~ (r2_hidden @ k1_xboole_0 @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['45', '46', '47', '48'])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      ((r2_hidden @ sk_C @ (k1_relat_1 @ (k8_relat_1 @ sk_D @ sk_E)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['26', '49'])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X13 @ (k1_relat_1 @ (k8_relat_1 @ X14 @ X15)))
% 0.20/0.50          | ((k1_funct_1 @ (k8_relat_1 @ X14 @ X15) @ X13)
% 0.20/0.50              = (k1_funct_1 @ X15 @ X13))
% 0.20/0.50          | ~ (v1_funct_1 @ X15)
% 0.20/0.50          | ~ (v1_relat_1 @ X15))),
% 0.20/0.50      inference('cnf', [status(esa)], [t87_funct_1])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ sk_E)
% 0.20/0.50        | ~ (v1_funct_1 @ sk_E)
% 0.20/0.50        | ((k1_funct_1 @ (k8_relat_1 @ sk_D @ sk_E) @ sk_C)
% 0.20/0.50            = (k1_funct_1 @ sk_E @ sk_C)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.50  thf('53', plain, ((v1_relat_1 @ sk_E)),
% 0.20/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('54', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('55', plain, (((k1_funct_1 @ sk_E @ sk_C) = (k1_xboole_0))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['19', '24'])).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      (((k1_funct_1 @ (k8_relat_1 @ sk_D @ sk_E) @ sk_C) = (k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      (((k1_funct_1 @ (k8_relat_1 @ sk_D @ sk_E) @ sk_C) != (k1_xboole_0))),
% 0.20/0.50      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.50  thf('58', plain, ($false),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['56', '57'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
