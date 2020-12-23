%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U6a7tsd6tb

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  110 (1088 expanded)
%              Number of leaves         :   28 ( 323 expanded)
%              Depth                    :   17
%              Number of atoms          :  728 (19631 expanded)
%              Number of equality atoms :   77 (1549 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(t85_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v2_funct_1 @ B )
       => ! [C: $i,D: $i] :
            ( ( ( r2_hidden @ C @ A )
              & ( r2_hidden @ D @ A )
              & ( ( k1_funct_1 @ B @ C )
                = ( k1_funct_1 @ B @ D ) ) )
           => ( C = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( v2_funct_1 @ B )
         => ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A )
                & ( ( k1_funct_1 @ B @ C )
                  = ( k1_funct_1 @ B @ D ) ) )
             => ( C = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t85_funct_2])).

thf('0',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    r1_tarski @ sk_B_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_B_1 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ D )
          & ( r2_hidden @ C @ A ) )
       => ( ( B = k1_xboole_0 )
          | ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) )
            = C ) ) ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ( X24 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ X25 ) @ ( k1_funct_1 @ X25 @ X22 ) )
        = X22 )
      | ~ ( v2_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t32_funct_2])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('14',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_1 ) )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('17',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_D ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_1 ) )
      = sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_C_1 = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    sk_C_1 != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('26',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('27',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('28',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('29',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('30',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('31',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference(demod,[status(thm)],['5','23','24','26','27','28','29','30'])).

thf('32',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference(demod,[status(thm)],['5','23','24','26','27','28','29','30'])).

thf('33',plain,
    ( ( k1_funct_1 @ k1_xboole_0 @ sk_C_1 )
    = ( k1_funct_1 @ k1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['0','31','32'])).

thf('34',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('35',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X16 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['44','47'])).

thf(d8_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
              & ( ( k1_funct_1 @ A @ B )
                = ( k1_funct_1 @ A @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('49',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X10 ) )
      | ( ( k1_funct_1 @ X10 @ X11 )
       != ( k1_funct_1 @ X10 @ X12 ) )
      | ( X11 = X12 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
       != ( k1_funct_1 @ k1_xboole_0 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v2_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('56',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('57',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('58',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['54','58'])).

thf('60',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['44','47'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
       != ( k1_funct_1 @ k1_xboole_0 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( v2_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['50','59','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference(demod,[status(thm)],['5','23','24','26','27','28','29','30'])).

thf('64',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference(demod,[status(thm)],['5','23','24','26','27','28','29','30'])).

thf('67',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ X0 )
       != ( k1_funct_1 @ k1_xboole_0 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['61','64','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ sk_C_1 )
       != ( k1_funct_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( sk_D = X0 )
      | ~ ( r2_hidden @ sk_D @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','68'])).

thf('70',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('72',plain,(
    r2_hidden @ sk_D @ k1_xboole_0 ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ sk_C_1 )
       != ( k1_funct_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( sk_D = X0 ) ) ),
    inference(demod,[status(thm)],['69','72'])).

thf('74',plain,
    ( ( sk_D = sk_C_1 )
    | ~ ( r2_hidden @ sk_C_1 @ k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['73'])).

thf('75',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('77',plain,(
    r2_hidden @ sk_C_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    sk_D = sk_C_1 ),
    inference(demod,[status(thm)],['74','77'])).

thf('79',plain,(
    sk_C_1 != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['78','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U6a7tsd6tb
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:20:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 133 iterations in 0.051s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.52  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.22/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.52  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.52  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.22/0.52  thf(t85_funct_2, conjecture,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.52       ( ( v2_funct_1 @ B ) =>
% 0.22/0.52         ( ![C:$i,D:$i]:
% 0.22/0.52           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.22/0.52               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.22/0.52             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i]:
% 0.22/0.52        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.52            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.52          ( ( v2_funct_1 @ B ) =>
% 0.22/0.52            ( ![C:$i,D:$i]:
% 0.22/0.52              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.22/0.52                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.22/0.52                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t85_funct_2])).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      (((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t3_subset, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (![X7 : $i, X8 : $i]:
% 0.22/0.52         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.52  thf('3', plain, ((r1_tarski @ sk_B_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.52  thf(d10_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X0 : $i, X2 : $i]:
% 0.22/0.52         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_B_1)
% 0.22/0.52        | ((k2_zfmisc_1 @ sk_A @ sk_A) = (sk_B_1)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.52  thf('6', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t32_funct_2, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.52       ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.22/0.52         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.52           ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.22/0.52             ( C ) ) ) ) ))).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X22 @ X23)
% 0.22/0.52          | ((X24) = (k1_xboole_0))
% 0.22/0.52          | ~ (v1_funct_1 @ X25)
% 0.22/0.52          | ~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.22/0.52          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.22/0.52          | ((k1_funct_1 @ (k2_funct_1 @ X25) @ (k1_funct_1 @ X25 @ X22))
% 0.22/0.52              = (X22))
% 0.22/0.52          | ~ (v2_funct_1 @ X25))),
% 0.22/0.52      inference('cnf', [status(esa)], [t32_funct_2])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v2_funct_1 @ sk_B_1)
% 0.22/0.52          | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.22/0.52              = (X0))
% 0.22/0.52          | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.22/0.52          | ~ (v1_funct_1 @ sk_B_1)
% 0.22/0.52          | ((sk_A) = (k1_xboole_0))
% 0.22/0.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.52  thf('10', plain, ((v2_funct_1 @ sk_B_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('11', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('12', plain, ((v1_funct_1 @ sk_B_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.22/0.52            = (X0))
% 0.22/0.52          | ((sk_A) = (k1_xboole_0))
% 0.22/0.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      ((((sk_A) = (k1_xboole_0))
% 0.22/0.52        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_1))
% 0.22/0.52            = (sk_C_1)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['6', '13'])).
% 0.22/0.52  thf('15', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.22/0.52            = (X0))
% 0.22/0.52          | ((sk_A) = (k1_xboole_0))
% 0.22/0.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      ((((sk_A) = (k1_xboole_0))
% 0.22/0.52        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.22/0.52            = (sk_D)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      ((((sk_A) = (k1_xboole_0))
% 0.22/0.52        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_1))
% 0.22/0.52            = (sk_D)))),
% 0.22/0.52      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      ((((sk_C_1) = (sk_D))
% 0.22/0.52        | ((sk_A) = (k1_xboole_0))
% 0.22/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['14', '19'])).
% 0.22/0.52  thf('21', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_1) = (sk_D)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['20'])).
% 0.22/0.52  thf('22', plain, (((sk_C_1) != (sk_D))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('23', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.22/0.52  thf('24', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.22/0.52  thf(t113_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X5 : $i, X6 : $i]:
% 0.22/0.52         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['25'])).
% 0.22/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.52  thf('27', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.52  thf('28', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.22/0.52  thf('29', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['25'])).
% 0.22/0.52  thf('31', plain, (((k1_xboole_0) = (sk_B_1))),
% 0.22/0.52      inference('demod', [status(thm)],
% 0.22/0.52                ['5', '23', '24', '26', '27', '28', '29', '30'])).
% 0.22/0.52  thf('32', plain, (((k1_xboole_0) = (sk_B_1))),
% 0.22/0.52      inference('demod', [status(thm)],
% 0.22/0.52                ['5', '23', '24', '26', '27', '28', '29', '30'])).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      (((k1_funct_1 @ k1_xboole_0 @ sk_C_1) = (k1_funct_1 @ k1_xboole_0 @ sk_D))),
% 0.22/0.52      inference('demod', [status(thm)], ['0', '31', '32'])).
% 0.22/0.52  thf('34', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      (![X7 : $i, X9 : $i]:
% 0.22/0.52         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.52  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.52         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.22/0.52          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.52  thf('39', plain,
% 0.22/0.52      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.52  thf(dt_k1_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.52         ((m1_subset_1 @ (k1_relset_1 @ X16 @ X17 @ X18) @ (k1_zfmisc_1 @ X16))
% 0.22/0.52          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.22/0.52  thf('41', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (m1_subset_1 @ (k1_relset_1 @ X1 @ X0 @ k1_xboole_0) @ 
% 0.22/0.52          (k1_zfmisc_1 @ X1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (m1_subset_1 @ (k1_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['38', '41'])).
% 0.22/0.52  thf('43', plain,
% 0.22/0.52      (![X7 : $i, X8 : $i]:
% 0.22/0.52         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.52  thf('44', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.22/0.52      inference('sup-', [status(thm)], ['42', '43'])).
% 0.22/0.52  thf('45', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.52  thf('46', plain,
% 0.22/0.52      (![X0 : $i, X2 : $i]:
% 0.22/0.52         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.52  thf('47', plain,
% 0.22/0.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.52  thf('48', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['44', '47'])).
% 0.22/0.52  thf(d8_funct_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.52       ( ( v2_funct_1 @ A ) <=>
% 0.22/0.52         ( ![B:$i,C:$i]:
% 0.22/0.52           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.22/0.52               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.22/0.52               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.22/0.52             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.22/0.52  thf('49', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.52         (~ (v2_funct_1 @ X10)
% 0.22/0.52          | ~ (r2_hidden @ X11 @ (k1_relat_1 @ X10))
% 0.22/0.52          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X10))
% 0.22/0.52          | ((k1_funct_1 @ X10 @ X11) != (k1_funct_1 @ X10 @ X12))
% 0.22/0.52          | ((X11) = (X12))
% 0.22/0.52          | ~ (v1_funct_1 @ X10)
% 0.22/0.52          | ~ (v1_relat_1 @ X10))),
% 0.22/0.52      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.22/0.52  thf('50', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.22/0.52          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.52          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.22/0.52          | ((X0) = (X1))
% 0.22/0.52          | ((k1_funct_1 @ k1_xboole_0 @ X0) != (k1_funct_1 @ k1_xboole_0 @ X1))
% 0.22/0.52          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ k1_xboole_0))
% 0.22/0.52          | ~ (v2_funct_1 @ k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.52  thf('51', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.52  thf('52', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.52      inference('simplify', [status(thm)], ['51'])).
% 0.22/0.52  thf('53', plain,
% 0.22/0.52      (![X7 : $i, X9 : $i]:
% 0.22/0.52         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.52  thf('54', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['52', '53'])).
% 0.22/0.52  thf('55', plain,
% 0.22/0.52      (![X5 : $i, X6 : $i]:
% 0.22/0.52         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.22/0.52  thf('56', plain,
% 0.22/0.52      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['55'])).
% 0.22/0.52  thf(cc1_relset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.52       ( v1_relat_1 @ C ) ))).
% 0.22/0.52  thf('57', plain,
% 0.22/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.52         ((v1_relat_1 @ X13)
% 0.22/0.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.52  thf('58', plain,
% 0.22/0.52      (![X1 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.22/0.52          | (v1_relat_1 @ X1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['56', '57'])).
% 0.22/0.52  thf('59', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.52      inference('sup-', [status(thm)], ['54', '58'])).
% 0.22/0.52  thf('60', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['44', '47'])).
% 0.22/0.52  thf('61', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.22/0.52          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.22/0.52          | ((X0) = (X1))
% 0.22/0.52          | ((k1_funct_1 @ k1_xboole_0 @ X0) != (k1_funct_1 @ k1_xboole_0 @ X1))
% 0.22/0.52          | ~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.22/0.52          | ~ (v2_funct_1 @ k1_xboole_0))),
% 0.22/0.52      inference('demod', [status(thm)], ['50', '59', '60'])).
% 0.22/0.52  thf('62', plain, ((v1_funct_1 @ sk_B_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('63', plain, (((k1_xboole_0) = (sk_B_1))),
% 0.22/0.52      inference('demod', [status(thm)],
% 0.22/0.52                ['5', '23', '24', '26', '27', '28', '29', '30'])).
% 0.22/0.52  thf('64', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.22/0.52      inference('demod', [status(thm)], ['62', '63'])).
% 0.22/0.52  thf('65', plain, ((v2_funct_1 @ sk_B_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('66', plain, (((k1_xboole_0) = (sk_B_1))),
% 0.22/0.52      inference('demod', [status(thm)],
% 0.22/0.52                ['5', '23', '24', '26', '27', '28', '29', '30'])).
% 0.22/0.52  thf('67', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.22/0.52      inference('demod', [status(thm)], ['65', '66'])).
% 0.22/0.52  thf('68', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.22/0.52          | ((X0) = (X1))
% 0.22/0.52          | ((k1_funct_1 @ k1_xboole_0 @ X0) != (k1_funct_1 @ k1_xboole_0 @ X1))
% 0.22/0.52          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.22/0.52      inference('demod', [status(thm)], ['61', '64', '67'])).
% 0.22/0.52  thf('69', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k1_funct_1 @ k1_xboole_0 @ sk_C_1)
% 0.22/0.52            != (k1_funct_1 @ k1_xboole_0 @ X0))
% 0.22/0.52          | ~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.22/0.52          | ((sk_D) = (X0))
% 0.22/0.52          | ~ (r2_hidden @ sk_D @ k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['33', '68'])).
% 0.22/0.52  thf('70', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('71', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.22/0.52  thf('72', plain, ((r2_hidden @ sk_D @ k1_xboole_0)),
% 0.22/0.52      inference('demod', [status(thm)], ['70', '71'])).
% 0.22/0.52  thf('73', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k1_funct_1 @ k1_xboole_0 @ sk_C_1)
% 0.22/0.52            != (k1_funct_1 @ k1_xboole_0 @ X0))
% 0.22/0.52          | ~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.22/0.52          | ((sk_D) = (X0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['69', '72'])).
% 0.22/0.52  thf('74', plain,
% 0.22/0.52      ((((sk_D) = (sk_C_1)) | ~ (r2_hidden @ sk_C_1 @ k1_xboole_0))),
% 0.22/0.52      inference('eq_res', [status(thm)], ['73'])).
% 0.22/0.52  thf('75', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('76', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['21', '22'])).
% 0.22/0.52  thf('77', plain, ((r2_hidden @ sk_C_1 @ k1_xboole_0)),
% 0.22/0.52      inference('demod', [status(thm)], ['75', '76'])).
% 0.22/0.52  thf('78', plain, (((sk_D) = (sk_C_1))),
% 0.22/0.52      inference('demod', [status(thm)], ['74', '77'])).
% 0.22/0.52  thf('79', plain, (((sk_C_1) != (sk_D))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('80', plain, ($false),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['78', '79'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
