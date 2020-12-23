%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QKgcx0sKGH

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:22 EST 2020

% Result     : Theorem 2.95s
% Output     : Refutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 411 expanded)
%              Number of leaves         :   40 ( 137 expanded)
%              Depth                    :   16
%              Number of atoms          : 1305 (7004 expanded)
%              Number of equality atoms :   55 ( 140 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t29_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
           => ( ( v2_funct_1 @ C )
              & ( v2_funct_2 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
             => ( ( v2_funct_1 @ C )
                & ( v2_funct_2 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('3',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('6',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('7',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('8',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('9',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('10',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('11',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('14',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('17',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_relset_1 @ X1 @ X0 @ X2 )
        = ( k2_relat_1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 )
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('24',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','14'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( v5_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v5_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('31',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_relat_1 @ X24 )
       != X23 )
      | ( v2_funct_2 @ X24 @ X23 )
      | ~ ( v5_relat_1 @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('32',plain,(
    ! [X24: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v5_relat_1 @ X24 @ ( k2_relat_1 @ X24 ) )
      | ( v2_funct_2 @ X24 @ ( k2_relat_1 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( v2_funct_2 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('36',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_funct_2 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_2 @ k1_xboole_0 @ ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_funct_2 @ k1_xboole_0 @ ( k2_relset_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['5','38'])).

thf('40',plain,
    ( ( v2_funct_2 @ k1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['2','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('42',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('43',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('44',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('45',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','46'])).

thf('48',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
           => ( ( k2_relset_1 @ A @ B @ C )
              = B ) ) ) ) )).

thf('53',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( r2_relset_1 @ X33 @ X33 @ ( k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35 ) @ ( k6_partfun1 @ X33 ) )
      | ( ( k2_relset_1 @ X34 @ X33 @ X35 )
        = X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['51','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('61',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['58','61','62','63','64'])).

thf('66',plain,(
    ! [X24: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v5_relat_1 @ X24 @ ( k2_relat_1 @ X24 ) )
      | ( v2_funct_2 @ X24 @ ( k2_relat_1 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('67',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('70',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['58','61','62','63','64'])).

thf('72',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('73',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('74',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('76',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['67','70','71','76'])).

thf('78',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['48'])).

thf('79',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['48'])).

thf('81',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['50','81'])).

thf('83',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['40','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('85',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('86',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('87',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('90',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['83','90'])).

thf('92',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('95',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['93','98'])).

thf('100',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('102',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['92','103'])).

thf('105',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('106',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf('108',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X39 @ X37 @ X37 @ X38 @ X40 @ X36 ) )
      | ( v2_funct_1 @ X40 )
      | ( X38 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X37 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['106','112'])).

thf('114',plain,(
    ! [X11: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X11 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('115',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','114','115','116','117'])).

thf('119',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['48'])).

thf('120',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['79','80'])).

thf('121',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['119','120'])).

thf('122',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['118','121'])).

thf('123',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('124',plain,(
    $false ),
    inference(demod,[status(thm)],['91','122','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QKgcx0sKGH
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:47:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 2.95/3.21  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.95/3.21  % Solved by: fo/fo7.sh
% 2.95/3.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.95/3.21  % done 3667 iterations in 2.757s
% 2.95/3.21  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.95/3.21  % SZS output start Refutation
% 2.95/3.21  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.95/3.21  thf(sk_B_type, type, sk_B: $i).
% 2.95/3.21  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.95/3.21  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.95/3.21  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.95/3.21  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.95/3.21  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.95/3.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.95/3.21  thf(sk_A_type, type, sk_A: $i).
% 2.95/3.21  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.95/3.21  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.95/3.21  thf(sk_C_type, type, sk_C: $i).
% 2.95/3.21  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.95/3.21  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 2.95/3.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.95/3.21  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.95/3.21  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.95/3.21  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.95/3.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.95/3.21  thf(sk_D_type, type, sk_D: $i).
% 2.95/3.21  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.95/3.21  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.95/3.21  thf(t29_funct_2, conjecture,
% 2.95/3.21    (![A:$i,B:$i,C:$i]:
% 2.95/3.21     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.95/3.21         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.95/3.21       ( ![D:$i]:
% 2.95/3.21         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.95/3.21             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.95/3.21           ( ( r2_relset_1 @
% 2.95/3.21               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.95/3.21               ( k6_partfun1 @ A ) ) =>
% 2.95/3.21             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 2.95/3.21  thf(zf_stmt_0, negated_conjecture,
% 2.95/3.21    (~( ![A:$i,B:$i,C:$i]:
% 2.95/3.21        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.95/3.21            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.95/3.21          ( ![D:$i]:
% 2.95/3.21            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.95/3.21                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.95/3.21              ( ( r2_relset_1 @
% 2.95/3.21                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.95/3.21                  ( k6_partfun1 @ A ) ) =>
% 2.95/3.21                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 2.95/3.21    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 2.95/3.21  thf('0', plain,
% 2.95/3.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.95/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.95/3.21  thf(redefinition_k2_relset_1, axiom,
% 2.95/3.21    (![A:$i,B:$i,C:$i]:
% 2.95/3.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.95/3.21       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.95/3.21  thf('1', plain,
% 2.95/3.21      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.95/3.21         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 2.95/3.21          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 2.95/3.21      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.95/3.21  thf('2', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 2.95/3.21      inference('sup-', [status(thm)], ['0', '1'])).
% 2.95/3.21  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.95/3.21  thf('3', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.95/3.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.95/3.21  thf(t8_boole, axiom,
% 2.95/3.21    (![A:$i,B:$i]:
% 2.95/3.21     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 2.95/3.21  thf('4', plain,
% 2.95/3.21      (![X0 : $i, X1 : $i]:
% 2.95/3.21         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 2.95/3.21      inference('cnf', [status(esa)], [t8_boole])).
% 2.95/3.21  thf('5', plain,
% 2.95/3.21      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.95/3.21      inference('sup-', [status(thm)], ['3', '4'])).
% 2.95/3.21  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 2.95/3.21  thf('6', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.95/3.21      inference('cnf', [status(esa)], [t81_relat_1])).
% 2.95/3.21  thf(redefinition_k6_partfun1, axiom,
% 2.95/3.21    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.95/3.21  thf('7', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 2.95/3.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.95/3.21  thf('8', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.95/3.21      inference('demod', [status(thm)], ['6', '7'])).
% 2.95/3.21  thf(t29_relset_1, axiom,
% 2.95/3.21    (![A:$i]:
% 2.95/3.21     ( m1_subset_1 @
% 2.95/3.21       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 2.95/3.21  thf('9', plain,
% 2.95/3.21      (![X22 : $i]:
% 2.95/3.21         (m1_subset_1 @ (k6_relat_1 @ X22) @ 
% 2.95/3.21          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 2.95/3.21      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.95/3.21  thf('10', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 2.95/3.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.95/3.21  thf('11', plain,
% 2.95/3.21      (![X22 : $i]:
% 2.95/3.21         (m1_subset_1 @ (k6_partfun1 @ X22) @ 
% 2.95/3.21          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 2.95/3.21      inference('demod', [status(thm)], ['9', '10'])).
% 2.95/3.21  thf('12', plain,
% 2.95/3.21      ((m1_subset_1 @ k1_xboole_0 @ 
% 2.95/3.21        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 2.95/3.21      inference('sup+', [status(thm)], ['8', '11'])).
% 2.95/3.21  thf(t113_zfmisc_1, axiom,
% 2.95/3.21    (![A:$i,B:$i]:
% 2.95/3.21     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.95/3.21       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.95/3.21  thf('13', plain,
% 2.95/3.21      (![X3 : $i, X4 : $i]:
% 2.95/3.21         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 2.95/3.21      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.95/3.21  thf('14', plain,
% 2.95/3.21      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 2.95/3.21      inference('simplify', [status(thm)], ['13'])).
% 2.95/3.21  thf('15', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 2.95/3.21      inference('demod', [status(thm)], ['12', '14'])).
% 2.95/3.21  thf('16', plain,
% 2.95/3.21      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.95/3.21      inference('sup-', [status(thm)], ['3', '4'])).
% 2.95/3.21  thf('17', plain,
% 2.95/3.21      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 2.95/3.21      inference('simplify', [status(thm)], ['13'])).
% 2.95/3.21  thf('18', plain,
% 2.95/3.21      (![X0 : $i, X1 : $i]:
% 2.95/3.21         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.95/3.21      inference('sup+', [status(thm)], ['16', '17'])).
% 2.95/3.21  thf('19', plain,
% 2.95/3.21      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.95/3.21         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 2.95/3.21          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 2.95/3.21      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.95/3.21  thf('20', plain,
% 2.95/3.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.95/3.21         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.95/3.21          | ~ (v1_xboole_0 @ X1)
% 2.95/3.21          | ((k2_relset_1 @ X1 @ X0 @ X2) = (k2_relat_1 @ X2)))),
% 2.95/3.21      inference('sup-', [status(thm)], ['18', '19'])).
% 2.95/3.21  thf('21', plain,
% 2.95/3.21      (![X0 : $i, X1 : $i]:
% 2.95/3.21         (((k2_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 2.95/3.21          | ~ (v1_xboole_0 @ X1))),
% 2.95/3.21      inference('sup-', [status(thm)], ['15', '20'])).
% 2.95/3.21  thf('22', plain,
% 2.95/3.21      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 2.95/3.21      inference('simplify', [status(thm)], ['13'])).
% 2.95/3.21  thf('23', plain,
% 2.95/3.21      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.95/3.21      inference('sup-', [status(thm)], ['3', '4'])).
% 2.95/3.21  thf('24', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 2.95/3.21      inference('demod', [status(thm)], ['12', '14'])).
% 2.95/3.21  thf('25', plain,
% 2.95/3.21      (![X0 : $i]:
% 2.95/3.21         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 2.95/3.21          | ~ (v1_xboole_0 @ X0))),
% 2.95/3.21      inference('sup+', [status(thm)], ['23', '24'])).
% 2.95/3.21  thf(cc2_relset_1, axiom,
% 2.95/3.21    (![A:$i,B:$i,C:$i]:
% 2.95/3.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.95/3.21       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.95/3.21  thf('26', plain,
% 2.95/3.21      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.95/3.21         ((v5_relat_1 @ X12 @ X14)
% 2.95/3.21          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 2.95/3.21      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.95/3.21  thf('27', plain,
% 2.95/3.21      (![X0 : $i, X1 : $i]:
% 2.95/3.21         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 2.95/3.21          | (v5_relat_1 @ k1_xboole_0 @ X0))),
% 2.95/3.21      inference('sup-', [status(thm)], ['25', '26'])).
% 2.95/3.21  thf('28', plain,
% 2.95/3.21      (![X0 : $i]:
% 2.95/3.21         (~ (v1_xboole_0 @ k1_xboole_0) | (v5_relat_1 @ k1_xboole_0 @ X0))),
% 2.95/3.21      inference('sup-', [status(thm)], ['22', '27'])).
% 2.95/3.21  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.95/3.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.95/3.21  thf('30', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 2.95/3.21      inference('demod', [status(thm)], ['28', '29'])).
% 2.95/3.21  thf(d3_funct_2, axiom,
% 2.95/3.21    (![A:$i,B:$i]:
% 2.95/3.21     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 2.95/3.21       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 2.95/3.21  thf('31', plain,
% 2.95/3.21      (![X23 : $i, X24 : $i]:
% 2.95/3.21         (((k2_relat_1 @ X24) != (X23))
% 2.95/3.21          | (v2_funct_2 @ X24 @ X23)
% 2.95/3.21          | ~ (v5_relat_1 @ X24 @ X23)
% 2.95/3.21          | ~ (v1_relat_1 @ X24))),
% 2.95/3.21      inference('cnf', [status(esa)], [d3_funct_2])).
% 2.95/3.21  thf('32', plain,
% 2.95/3.21      (![X24 : $i]:
% 2.95/3.21         (~ (v1_relat_1 @ X24)
% 2.95/3.21          | ~ (v5_relat_1 @ X24 @ (k2_relat_1 @ X24))
% 2.95/3.21          | (v2_funct_2 @ X24 @ (k2_relat_1 @ X24)))),
% 2.95/3.21      inference('simplify', [status(thm)], ['31'])).
% 2.95/3.21  thf('33', plain,
% 2.95/3.21      (((v2_funct_2 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0))
% 2.95/3.21        | ~ (v1_relat_1 @ k1_xboole_0))),
% 2.95/3.21      inference('sup-', [status(thm)], ['30', '32'])).
% 2.95/3.21  thf('34', plain,
% 2.95/3.21      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 2.95/3.21      inference('simplify', [status(thm)], ['13'])).
% 2.95/3.21  thf(fc6_relat_1, axiom,
% 2.95/3.21    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.95/3.21  thf('35', plain,
% 2.95/3.21      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 2.95/3.21      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.95/3.21  thf('36', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.95/3.21      inference('sup+', [status(thm)], ['34', '35'])).
% 2.95/3.21  thf('37', plain, ((v2_funct_2 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0))),
% 2.95/3.21      inference('demod', [status(thm)], ['33', '36'])).
% 2.95/3.21  thf('38', plain,
% 2.95/3.21      (![X0 : $i, X1 : $i]:
% 2.95/3.21         ((v2_funct_2 @ k1_xboole_0 @ (k2_relset_1 @ X1 @ X0 @ k1_xboole_0))
% 2.95/3.21          | ~ (v1_xboole_0 @ X1))),
% 2.95/3.21      inference('sup+', [status(thm)], ['21', '37'])).
% 2.95/3.21  thf('39', plain,
% 2.95/3.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.95/3.21         ((v2_funct_2 @ k1_xboole_0 @ (k2_relset_1 @ X2 @ X1 @ X0))
% 2.95/3.21          | ~ (v1_xboole_0 @ X0)
% 2.95/3.21          | ~ (v1_xboole_0 @ X2))),
% 2.95/3.21      inference('sup+', [status(thm)], ['5', '38'])).
% 2.95/3.21  thf('40', plain,
% 2.95/3.21      (((v2_funct_2 @ k1_xboole_0 @ (k2_relat_1 @ sk_C))
% 2.95/3.21        | ~ (v1_xboole_0 @ sk_A)
% 2.95/3.21        | ~ (v1_xboole_0 @ sk_C))),
% 2.95/3.21      inference('sup+', [status(thm)], ['2', '39'])).
% 2.95/3.21  thf('41', plain,
% 2.95/3.21      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.95/3.21      inference('sup-', [status(thm)], ['3', '4'])).
% 2.95/3.21  thf('42', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.95/3.21      inference('demod', [status(thm)], ['6', '7'])).
% 2.95/3.21  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 2.95/3.21  thf('43', plain, (![X11 : $i]: (v2_funct_1 @ (k6_relat_1 @ X11))),
% 2.95/3.21      inference('cnf', [status(esa)], [t52_funct_1])).
% 2.95/3.21  thf('44', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 2.95/3.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.95/3.21  thf('45', plain, (![X11 : $i]: (v2_funct_1 @ (k6_partfun1 @ X11))),
% 2.95/3.21      inference('demod', [status(thm)], ['43', '44'])).
% 2.95/3.21  thf('46', plain, ((v2_funct_1 @ k1_xboole_0)),
% 2.95/3.21      inference('sup+', [status(thm)], ['42', '45'])).
% 2.95/3.21  thf('47', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 2.95/3.21      inference('sup+', [status(thm)], ['41', '46'])).
% 2.95/3.21  thf('48', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 2.95/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.95/3.21  thf('49', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.95/3.21      inference('split', [status(esa)], ['48'])).
% 2.95/3.21  thf('50', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.95/3.21      inference('sup-', [status(thm)], ['47', '49'])).
% 2.95/3.21  thf('51', plain,
% 2.95/3.21      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.95/3.21        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.95/3.21        (k6_partfun1 @ sk_A))),
% 2.95/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.95/3.21  thf('52', plain,
% 2.95/3.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.95/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.95/3.21  thf(t24_funct_2, axiom,
% 2.95/3.21    (![A:$i,B:$i,C:$i]:
% 2.95/3.21     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.95/3.21         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.95/3.21       ( ![D:$i]:
% 2.95/3.21         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.95/3.21             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.95/3.21           ( ( r2_relset_1 @
% 2.95/3.21               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.95/3.21               ( k6_partfun1 @ B ) ) =>
% 2.95/3.21             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.95/3.21  thf('53', plain,
% 2.95/3.21      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 2.95/3.21         (~ (v1_funct_1 @ X32)
% 2.95/3.21          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 2.95/3.21          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 2.95/3.21          | ~ (r2_relset_1 @ X33 @ X33 @ 
% 2.95/3.21               (k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35) @ 
% 2.95/3.21               (k6_partfun1 @ X33))
% 2.95/3.21          | ((k2_relset_1 @ X34 @ X33 @ X35) = (X33))
% 2.95/3.21          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 2.95/3.21          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 2.95/3.21          | ~ (v1_funct_1 @ X35))),
% 2.95/3.21      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.95/3.21  thf('54', plain,
% 2.95/3.21      (![X0 : $i]:
% 2.95/3.21         (~ (v1_funct_1 @ X0)
% 2.95/3.21          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.95/3.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.95/3.21          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.95/3.21          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.95/3.21               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.95/3.21               (k6_partfun1 @ sk_A))
% 2.95/3.21          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.95/3.21          | ~ (v1_funct_1 @ sk_C))),
% 2.95/3.21      inference('sup-', [status(thm)], ['52', '53'])).
% 2.95/3.21  thf('55', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.95/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.95/3.21  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 2.95/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.95/3.21  thf('57', plain,
% 2.95/3.21      (![X0 : $i]:
% 2.95/3.21         (~ (v1_funct_1 @ X0)
% 2.95/3.21          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.95/3.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.95/3.21          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.95/3.21          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.95/3.21               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.95/3.21               (k6_partfun1 @ sk_A)))),
% 2.95/3.21      inference('demod', [status(thm)], ['54', '55', '56'])).
% 2.95/3.21  thf('58', plain,
% 2.95/3.21      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 2.95/3.21        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.95/3.21        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.95/3.21        | ~ (v1_funct_1 @ sk_D))),
% 2.95/3.21      inference('sup-', [status(thm)], ['51', '57'])).
% 2.95/3.21  thf('59', plain,
% 2.95/3.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.95/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.95/3.21  thf('60', plain,
% 2.95/3.21      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.95/3.21         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 2.95/3.21          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 2.95/3.21      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.95/3.21  thf('61', plain,
% 2.95/3.21      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.95/3.21      inference('sup-', [status(thm)], ['59', '60'])).
% 2.95/3.21  thf('62', plain,
% 2.95/3.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.95/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.95/3.21  thf('63', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.95/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.95/3.21  thf('64', plain, ((v1_funct_1 @ sk_D)),
% 2.95/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.95/3.21  thf('65', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.95/3.21      inference('demod', [status(thm)], ['58', '61', '62', '63', '64'])).
% 2.95/3.21  thf('66', plain,
% 2.95/3.21      (![X24 : $i]:
% 2.95/3.21         (~ (v1_relat_1 @ X24)
% 2.95/3.21          | ~ (v5_relat_1 @ X24 @ (k2_relat_1 @ X24))
% 2.95/3.21          | (v2_funct_2 @ X24 @ (k2_relat_1 @ X24)))),
% 2.95/3.21      inference('simplify', [status(thm)], ['31'])).
% 2.95/3.21  thf('67', plain,
% 2.95/3.21      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 2.95/3.21        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 2.95/3.21        | ~ (v1_relat_1 @ sk_D))),
% 2.95/3.21      inference('sup-', [status(thm)], ['65', '66'])).
% 2.95/3.21  thf('68', plain,
% 2.95/3.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.95/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.95/3.21  thf('69', plain,
% 2.95/3.21      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.95/3.21         ((v5_relat_1 @ X12 @ X14)
% 2.95/3.21          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 2.95/3.21      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.95/3.21  thf('70', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 2.95/3.21      inference('sup-', [status(thm)], ['68', '69'])).
% 2.95/3.21  thf('71', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.95/3.21      inference('demod', [status(thm)], ['58', '61', '62', '63', '64'])).
% 2.95/3.21  thf('72', plain,
% 2.95/3.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.95/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.95/3.21  thf(cc2_relat_1, axiom,
% 2.95/3.21    (![A:$i]:
% 2.95/3.21     ( ( v1_relat_1 @ A ) =>
% 2.95/3.21       ( ![B:$i]:
% 2.95/3.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.95/3.21  thf('73', plain,
% 2.95/3.21      (![X7 : $i, X8 : $i]:
% 2.95/3.21         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 2.95/3.21          | (v1_relat_1 @ X7)
% 2.95/3.21          | ~ (v1_relat_1 @ X8))),
% 2.95/3.21      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.95/3.21  thf('74', plain,
% 2.95/3.21      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 2.95/3.21      inference('sup-', [status(thm)], ['72', '73'])).
% 2.95/3.21  thf('75', plain,
% 2.95/3.21      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 2.95/3.21      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.95/3.21  thf('76', plain, ((v1_relat_1 @ sk_D)),
% 2.95/3.21      inference('demod', [status(thm)], ['74', '75'])).
% 2.95/3.21  thf('77', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 2.95/3.21      inference('demod', [status(thm)], ['67', '70', '71', '76'])).
% 2.95/3.21  thf('78', plain,
% 2.95/3.21      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 2.95/3.21      inference('split', [status(esa)], ['48'])).
% 2.95/3.21  thf('79', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 2.95/3.21      inference('sup-', [status(thm)], ['77', '78'])).
% 2.95/3.21  thf('80', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 2.95/3.21      inference('split', [status(esa)], ['48'])).
% 2.95/3.21  thf('81', plain, (~ ((v2_funct_1 @ sk_C))),
% 2.95/3.21      inference('sat_resolution*', [status(thm)], ['79', '80'])).
% 2.95/3.21  thf('82', plain, (~ (v1_xboole_0 @ sk_C)),
% 2.95/3.21      inference('simpl_trail', [status(thm)], ['50', '81'])).
% 2.95/3.21  thf('83', plain, ((~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 2.95/3.21      inference('clc', [status(thm)], ['40', '82'])).
% 2.95/3.21  thf('84', plain,
% 2.95/3.21      (![X0 : $i, X1 : $i]:
% 2.95/3.21         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 2.95/3.21      inference('sup+', [status(thm)], ['16', '17'])).
% 2.95/3.21  thf('85', plain,
% 2.95/3.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.95/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.95/3.21  thf(cc1_subset_1, axiom,
% 2.95/3.21    (![A:$i]:
% 2.95/3.21     ( ( v1_xboole_0 @ A ) =>
% 2.95/3.21       ( ![B:$i]:
% 2.95/3.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 2.95/3.21  thf('86', plain,
% 2.95/3.21      (![X5 : $i, X6 : $i]:
% 2.95/3.21         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 2.95/3.21          | (v1_xboole_0 @ X5)
% 2.95/3.21          | ~ (v1_xboole_0 @ X6))),
% 2.95/3.21      inference('cnf', [status(esa)], [cc1_subset_1])).
% 2.95/3.21  thf('87', plain,
% 2.95/3.21      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 2.95/3.21      inference('sup-', [status(thm)], ['85', '86'])).
% 2.95/3.21  thf('88', plain,
% 2.95/3.21      ((~ (v1_xboole_0 @ k1_xboole_0)
% 2.95/3.21        | ~ (v1_xboole_0 @ sk_A)
% 2.95/3.21        | (v1_xboole_0 @ sk_C))),
% 2.95/3.21      inference('sup-', [status(thm)], ['84', '87'])).
% 2.95/3.21  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.95/3.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.95/3.21  thf('90', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 2.95/3.21      inference('demod', [status(thm)], ['88', '89'])).
% 2.95/3.21  thf('91', plain, (~ (v1_xboole_0 @ sk_A)),
% 2.95/3.21      inference('clc', [status(thm)], ['83', '90'])).
% 2.95/3.21  thf('92', plain,
% 2.95/3.21      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.95/3.21        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.95/3.21        (k6_partfun1 @ sk_A))),
% 2.95/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.95/3.21  thf('93', plain,
% 2.95/3.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.95/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.95/3.21  thf('94', plain,
% 2.95/3.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.95/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.95/3.21  thf(dt_k1_partfun1, axiom,
% 2.95/3.21    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.95/3.21     ( ( ( v1_funct_1 @ E ) & 
% 2.95/3.21         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.95/3.21         ( v1_funct_1 @ F ) & 
% 2.95/3.21         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.95/3.21       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.95/3.21         ( m1_subset_1 @
% 2.95/3.21           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.95/3.21           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.95/3.21  thf('95', plain,
% 2.95/3.21      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 2.95/3.21         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 2.95/3.21          | ~ (v1_funct_1 @ X25)
% 2.95/3.21          | ~ (v1_funct_1 @ X28)
% 2.95/3.21          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 2.95/3.21          | (m1_subset_1 @ (k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28) @ 
% 2.95/3.21             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X30))))),
% 2.95/3.21      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.95/3.21  thf('96', plain,
% 2.95/3.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.95/3.21         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.95/3.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.95/3.21          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.95/3.21          | ~ (v1_funct_1 @ X1)
% 2.95/3.21          | ~ (v1_funct_1 @ sk_C))),
% 2.95/3.21      inference('sup-', [status(thm)], ['94', '95'])).
% 2.95/3.21  thf('97', plain, ((v1_funct_1 @ sk_C)),
% 2.95/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.95/3.21  thf('98', plain,
% 2.95/3.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.95/3.21         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.95/3.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.95/3.21          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.95/3.21          | ~ (v1_funct_1 @ X1))),
% 2.95/3.21      inference('demod', [status(thm)], ['96', '97'])).
% 2.95/3.21  thf('99', plain,
% 2.95/3.21      ((~ (v1_funct_1 @ sk_D)
% 2.95/3.21        | (m1_subset_1 @ 
% 2.95/3.21           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.95/3.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.95/3.21      inference('sup-', [status(thm)], ['93', '98'])).
% 2.95/3.21  thf('100', plain, ((v1_funct_1 @ sk_D)),
% 2.95/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.95/3.21  thf('101', plain,
% 2.95/3.21      ((m1_subset_1 @ 
% 2.95/3.21        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.95/3.21        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.95/3.21      inference('demod', [status(thm)], ['99', '100'])).
% 2.95/3.21  thf(redefinition_r2_relset_1, axiom,
% 2.95/3.21    (![A:$i,B:$i,C:$i,D:$i]:
% 2.95/3.21     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.95/3.21         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.95/3.21       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.95/3.21  thf('102', plain,
% 2.95/3.21      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 2.95/3.21         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 2.95/3.21          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 2.95/3.21          | ((X18) = (X21))
% 2.95/3.21          | ~ (r2_relset_1 @ X19 @ X20 @ X18 @ X21))),
% 2.95/3.21      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.95/3.21  thf('103', plain,
% 2.95/3.21      (![X0 : $i]:
% 2.95/3.21         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.95/3.21             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 2.95/3.21          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 2.95/3.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.95/3.21      inference('sup-', [status(thm)], ['101', '102'])).
% 2.95/3.21  thf('104', plain,
% 2.95/3.21      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 2.95/3.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.95/3.21        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.95/3.21            = (k6_partfun1 @ sk_A)))),
% 2.95/3.21      inference('sup-', [status(thm)], ['92', '103'])).
% 2.95/3.21  thf('105', plain,
% 2.95/3.21      (![X22 : $i]:
% 2.95/3.21         (m1_subset_1 @ (k6_partfun1 @ X22) @ 
% 2.95/3.21          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 2.95/3.21      inference('demod', [status(thm)], ['9', '10'])).
% 2.95/3.21  thf('106', plain,
% 2.95/3.21      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.95/3.21         = (k6_partfun1 @ sk_A))),
% 2.95/3.21      inference('demod', [status(thm)], ['104', '105'])).
% 2.95/3.21  thf('107', plain,
% 2.95/3.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.95/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.95/3.21  thf(t26_funct_2, axiom,
% 2.95/3.21    (![A:$i,B:$i,C:$i,D:$i]:
% 2.95/3.21     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.95/3.21         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.95/3.21       ( ![E:$i]:
% 2.95/3.21         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.95/3.21             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.95/3.21           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 2.95/3.21             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 2.95/3.21               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 2.95/3.21  thf('108', plain,
% 2.95/3.21      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 2.95/3.21         (~ (v1_funct_1 @ X36)
% 2.95/3.21          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 2.95/3.21          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 2.95/3.21          | ~ (v2_funct_1 @ (k1_partfun1 @ X39 @ X37 @ X37 @ X38 @ X40 @ X36))
% 2.95/3.21          | (v2_funct_1 @ X40)
% 2.95/3.21          | ((X38) = (k1_xboole_0))
% 2.95/3.21          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X37)))
% 2.95/3.21          | ~ (v1_funct_2 @ X40 @ X39 @ X37)
% 2.95/3.21          | ~ (v1_funct_1 @ X40))),
% 2.95/3.21      inference('cnf', [status(esa)], [t26_funct_2])).
% 2.95/3.21  thf('109', plain,
% 2.95/3.21      (![X0 : $i, X1 : $i]:
% 2.95/3.21         (~ (v1_funct_1 @ X0)
% 2.95/3.21          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.95/3.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.95/3.21          | ((sk_A) = (k1_xboole_0))
% 2.95/3.21          | (v2_funct_1 @ X0)
% 2.95/3.21          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.95/3.21          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.95/3.21          | ~ (v1_funct_1 @ sk_D))),
% 2.95/3.21      inference('sup-', [status(thm)], ['107', '108'])).
% 2.95/3.21  thf('110', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.95/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.95/3.21  thf('111', plain, ((v1_funct_1 @ sk_D)),
% 2.95/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.95/3.21  thf('112', plain,
% 2.95/3.21      (![X0 : $i, X1 : $i]:
% 2.95/3.21         (~ (v1_funct_1 @ X0)
% 2.95/3.21          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.95/3.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.95/3.21          | ((sk_A) = (k1_xboole_0))
% 2.95/3.21          | (v2_funct_1 @ X0)
% 2.95/3.21          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 2.95/3.21      inference('demod', [status(thm)], ['109', '110', '111'])).
% 2.95/3.21  thf('113', plain,
% 2.95/3.21      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 2.95/3.21        | (v2_funct_1 @ sk_C)
% 2.95/3.21        | ((sk_A) = (k1_xboole_0))
% 2.95/3.21        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.95/3.21        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.95/3.21        | ~ (v1_funct_1 @ sk_C))),
% 2.95/3.21      inference('sup-', [status(thm)], ['106', '112'])).
% 2.95/3.21  thf('114', plain, (![X11 : $i]: (v2_funct_1 @ (k6_partfun1 @ X11))),
% 2.95/3.21      inference('demod', [status(thm)], ['43', '44'])).
% 2.95/3.21  thf('115', plain,
% 2.95/3.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.95/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.95/3.21  thf('116', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.95/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.95/3.21  thf('117', plain, ((v1_funct_1 @ sk_C)),
% 2.95/3.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.95/3.21  thf('118', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.95/3.21      inference('demod', [status(thm)], ['113', '114', '115', '116', '117'])).
% 2.95/3.21  thf('119', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.95/3.21      inference('split', [status(esa)], ['48'])).
% 2.95/3.21  thf('120', plain, (~ ((v2_funct_1 @ sk_C))),
% 2.95/3.21      inference('sat_resolution*', [status(thm)], ['79', '80'])).
% 2.95/3.21  thf('121', plain, (~ (v2_funct_1 @ sk_C)),
% 2.95/3.21      inference('simpl_trail', [status(thm)], ['119', '120'])).
% 2.95/3.21  thf('122', plain, (((sk_A) = (k1_xboole_0))),
% 2.95/3.21      inference('clc', [status(thm)], ['118', '121'])).
% 2.95/3.21  thf('123', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.95/3.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.95/3.21  thf('124', plain, ($false),
% 2.95/3.21      inference('demod', [status(thm)], ['91', '122', '123'])).
% 2.95/3.21  
% 2.95/3.21  % SZS output end Refutation
% 2.95/3.21  
% 2.95/3.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
