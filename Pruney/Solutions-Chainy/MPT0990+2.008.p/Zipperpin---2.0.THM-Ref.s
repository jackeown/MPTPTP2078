%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HyQ29ShtGD

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:54 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  338 (2044 expanded)
%              Number of leaves         :   48 ( 650 expanded)
%              Depth                    :   42
%              Number of atoms          : 2784 (39458 expanded)
%              Number of equality atoms :  166 (2678 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k5_relat_1 @ X21 @ ( k2_funct_1 @ X21 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k5_relat_1 @ X21 @ ( k2_funct_1 @ X21 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('5',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X21 ) @ X21 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('6',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('7',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X21 ) @ X21 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X21 ) @ X21 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('9',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X21 ) @ X21 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('10',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X21 ) @ X21 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('11',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X21 ) @ X21 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('12',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relat_1 @ X20 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('14',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t36_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( v2_funct_1 @ C ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ C )
                  = B )
                & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( v2_funct_1 @ C ) )
             => ( ( A = k1_xboole_0 )
                | ( B = k1_xboole_0 )
                | ( D
                  = ( k2_funct_1 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_funct_2])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('16',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('17',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('21',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relat_1 @ X20 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ( v4_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['19','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('31',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['29','32','33','34'])).

thf('36',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['13','43'])).

thf('45',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['17','18'])).

thf('46',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('48',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['44','45','46','47','48','49'])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('51',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ( v4_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ( v4_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v4_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','58'])).

thf('60',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('61',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('62',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('63',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('70',plain,(
    v4_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['59','60','65','66','67','68','69'])).

thf('71',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','72'])).

thf('74',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['17','18'])).

thf('75',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('76',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['73','74','75','76','77','78'])).

thf('80',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('81',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['9','81'])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('84',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('85',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('86',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('88',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('89',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['82','83','86','87','88','89','90'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('92',plain,(
    ! [X15: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X15 ) ) @ X15 )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('93',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('94',plain,(
    ! [X15: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X15 ) ) @ X15 )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['91','94'])).

thf('96',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','95'])).

thf('97',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['17','18'])).

thf('98',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('99',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('100',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['96','97','98','99','100','101'])).

thf('103',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['7','102'])).

thf('104',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['17','18'])).

thf('105',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('106',plain,(
    ! [X15: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X15 ) ) @ X15 )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('111',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( k6_partfun1 @ sk_B )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['103','104','109','110','111','112'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('114',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) @ X12 )
        = ( k5_relat_1 @ X11 @ ( k5_relat_1 @ X10 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','117'])).

thf('119',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('120',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('122',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['3','121'])).

thf('123',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('124',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['44','45','46','47','48','49'])).

thf('125',plain,(
    ! [X15: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X15 ) ) @ X15 )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('126',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['123','126'])).

thf('128',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('129',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('132',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['122','130','131','132','133'])).

thf('135',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['0','134'])).

thf('136',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('137',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('141',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( ( k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45 )
        = ( k5_relat_1 @ X42 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('142',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['139','144'])).

thf('146',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
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

thf('150',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['148','153'])).

thf('155',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('157',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( X31 = X34 )
      | ~ ( r2_relset_1 @ X32 @ X33 @ X31 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['147','158'])).

thf('160',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('161',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['145','146','161'])).

thf('163',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('164',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['162','165'])).

thf('167',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('168',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('169',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('170',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('172',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('174',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['145','146','161'])).

thf('176',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('177',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('179',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('181',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['166','167','174','175','176','179','180'])).

thf('182',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['138','181'])).

thf('183',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['145','146','161'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('185',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['183','184'])).

thf('186',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['177','178'])).

thf('187',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['185','186'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('188',plain,(
    ! [X5: $i] :
      ( ( ( k10_relat_1 @ X5 @ ( k2_relat_1 @ X5 ) )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('189',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k10_relat_1 @ X7 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('190',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ X16 @ ( k6_relat_1 @ ( k2_relat_1 @ X16 ) ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('191',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('192',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ X16 @ ( k6_partfun1 @ ( k2_relat_1 @ X16 ) ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('195',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('197',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['177','178'])).

thf('199',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X5: $i] :
      ( ( ( k10_relat_1 @ X5 @ ( k2_relat_1 @ X5 ) )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('201',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ X16 @ ( k6_partfun1 @ ( k2_relat_1 @ X16 ) ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('202',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('203',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k10_relat_1 @ X7 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('204',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ( v4_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('205',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X2 @ X0 ) @ X1 )
      | ( v4_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_partfun1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['202','205'])).

thf('207',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('208',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X2 @ X0 ) @ X1 )
      | ( v4_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_partfun1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) @ X1 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['201','208'])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) @ X1 )
      | ( v4_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['209'])).

thf('211',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['200','210'])).

thf('212',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['211'])).

thf('213',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( v4_relat_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['199','212'])).

thf('214',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['177','178'])).

thf('215',plain,(
    v4_relat_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) @ sk_B ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('217',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['192','217'])).

thf('219',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['177','178'])).

thf('220',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['177','178'])).

thf('221',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ) @ sk_B ),
    inference(demod,[status(thm)],['218','219','220'])).

thf('222',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_D @ ( k1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['189','221'])).

thf('223',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('224',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['177','178'])).

thf('225',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('226',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_D @ ( k2_relat_1 @ sk_D ) ) @ sk_B ),
    inference(demod,[status(thm)],['222','223','224','225'])).

thf('227',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('228',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ ( k2_relat_1 @ X19 ) )
      | ( ( k9_relat_1 @ X19 @ ( k10_relat_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('229',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('231',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['229','230','231'])).

thf('233',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k10_relat_1 @ sk_D @ ( k2_relat_1 @ sk_D ) ) ) )
    = ( k10_relat_1 @ sk_D @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['226','232'])).

thf('234',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
      = ( k10_relat_1 @ sk_D @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['188','233'])).

thf('235',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['197','198'])).

thf('236',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['229','230','231'])).

thf('237',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('238',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['177','178'])).

thf('239',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k10_relat_1 @ sk_D @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['234','237','238'])).

thf('240',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ X16 @ ( k6_partfun1 @ ( k2_relat_1 @ X16 ) ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('241',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k10_relat_1 @ X7 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('242',plain,(
    ! [X15: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X15 ) ) @ X15 )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('243',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['241','242'])).

thf('244',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['240','243'])).

thf('245',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('246',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('247',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['244','245','246'])).

thf('248',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf('249',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) )
      = ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['239','248'])).

thf('250',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['177','178'])).

thf('251',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) )
    = ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['249','250'])).

thf('252',plain,(
    ! [X15: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X15 ) ) @ X15 )
        = X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('253',plain,(
    ! [X16: $i] :
      ( ( ( k5_relat_1 @ X16 @ ( k6_partfun1 @ ( k2_relat_1 @ X16 ) ) )
        = X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('254',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) )
    = ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['249','250'])).

thf('255',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D )
      = ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['253','254'])).

thf('256',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['177','178'])).

thf('257',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D )
    = ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['255','256'])).

thf('258',plain,
    ( ( sk_D
      = ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['252','257'])).

thf('259',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['177','178'])).

thf('260',plain,
    ( sk_D
    = ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['258','259'])).

thf('261',plain,
    ( sk_D
    = ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['258','259'])).

thf('262',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['251','260','261'])).

thf('263',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('264',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['145','146','161'])).

thf('265',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k10_relat_1 @ X7 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('266',plain,
    ( ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
      = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['264','265'])).

thf('267',plain,(
    ! [X13: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('268',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('269',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['177','178'])).

thf('270',plain,
    ( sk_A
    = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['266','267','268','269'])).

thf('271',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['263','270'])).

thf('272',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('273',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['229','230','231'])).

thf('274',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['272','273'])).

thf('275',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['17','18'])).

thf('276',plain,(
    ! [X5: $i] :
      ( ( ( k10_relat_1 @ X5 @ ( k2_relat_1 @ X5 ) )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('277',plain,
    ( ( ( k10_relat_1 @ sk_C @ sk_B )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['275','276'])).

thf('278',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['30','31'])).

thf('279',plain,
    ( ( k10_relat_1 @ sk_C @ sk_B )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['277','278'])).

thf('280',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['274','279'])).

thf('281',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['166','167','174','175','176','179','180'])).

thf('282',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['280','281'])).

thf('283',plain,
    ( ( k1_relat_1 @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['271','282'])).

thf('284',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['262','283'])).

thf('285',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['187','284'])).

thf('286',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['182','285'])).

thf('287',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('288',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['286','287'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HyQ29ShtGD
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:41:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 1.65/1.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.65/1.87  % Solved by: fo/fo7.sh
% 1.65/1.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.65/1.87  % done 1890 iterations in 1.419s
% 1.65/1.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.65/1.87  % SZS output start Refutation
% 1.65/1.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.65/1.87  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.65/1.87  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.65/1.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.65/1.87  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.65/1.87  thf(sk_A_type, type, sk_A: $i).
% 1.65/1.87  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.65/1.87  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.65/1.87  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.65/1.87  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.65/1.87  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.65/1.87  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.65/1.87  thf(sk_B_type, type, sk_B: $i).
% 1.65/1.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.65/1.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.65/1.87  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.65/1.87  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.65/1.87  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.65/1.87  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.65/1.87  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.65/1.87  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.65/1.87  thf(sk_D_type, type, sk_D: $i).
% 1.65/1.87  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.65/1.87  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.65/1.87  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.65/1.87  thf(sk_C_type, type, sk_C: $i).
% 1.65/1.87  thf(dt_k2_funct_1, axiom,
% 1.65/1.87    (![A:$i]:
% 1.65/1.87     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.65/1.87       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.65/1.87         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.65/1.87  thf('0', plain,
% 1.65/1.87      (![X17 : $i]:
% 1.65/1.87         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 1.65/1.87          | ~ (v1_funct_1 @ X17)
% 1.65/1.87          | ~ (v1_relat_1 @ X17))),
% 1.65/1.87      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.65/1.87  thf(t61_funct_1, axiom,
% 1.65/1.87    (![A:$i]:
% 1.65/1.87     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.65/1.87       ( ( v2_funct_1 @ A ) =>
% 1.65/1.87         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.65/1.87             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.65/1.87           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.65/1.87             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.65/1.87  thf('1', plain,
% 1.65/1.87      (![X21 : $i]:
% 1.65/1.87         (~ (v2_funct_1 @ X21)
% 1.65/1.87          | ((k5_relat_1 @ X21 @ (k2_funct_1 @ X21))
% 1.65/1.87              = (k6_relat_1 @ (k1_relat_1 @ X21)))
% 1.65/1.87          | ~ (v1_funct_1 @ X21)
% 1.65/1.87          | ~ (v1_relat_1 @ X21))),
% 1.65/1.87      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.65/1.87  thf(redefinition_k6_partfun1, axiom,
% 1.65/1.87    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.65/1.87  thf('2', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 1.65/1.87      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.65/1.87  thf('3', plain,
% 1.65/1.87      (![X21 : $i]:
% 1.65/1.87         (~ (v2_funct_1 @ X21)
% 1.65/1.87          | ((k5_relat_1 @ X21 @ (k2_funct_1 @ X21))
% 1.65/1.87              = (k6_partfun1 @ (k1_relat_1 @ X21)))
% 1.65/1.87          | ~ (v1_funct_1 @ X21)
% 1.65/1.87          | ~ (v1_relat_1 @ X21))),
% 1.65/1.87      inference('demod', [status(thm)], ['1', '2'])).
% 1.65/1.87  thf('4', plain,
% 1.65/1.87      (![X17 : $i]:
% 1.65/1.87         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 1.65/1.87          | ~ (v1_funct_1 @ X17)
% 1.65/1.87          | ~ (v1_relat_1 @ X17))),
% 1.65/1.87      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.65/1.87  thf('5', plain,
% 1.65/1.87      (![X21 : $i]:
% 1.65/1.87         (~ (v2_funct_1 @ X21)
% 1.65/1.87          | ((k5_relat_1 @ (k2_funct_1 @ X21) @ X21)
% 1.65/1.87              = (k6_relat_1 @ (k2_relat_1 @ X21)))
% 1.65/1.87          | ~ (v1_funct_1 @ X21)
% 1.65/1.87          | ~ (v1_relat_1 @ X21))),
% 1.65/1.87      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.65/1.87  thf('6', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 1.65/1.87      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.65/1.87  thf('7', plain,
% 1.65/1.87      (![X21 : $i]:
% 1.65/1.87         (~ (v2_funct_1 @ X21)
% 1.65/1.87          | ((k5_relat_1 @ (k2_funct_1 @ X21) @ X21)
% 1.65/1.87              = (k6_partfun1 @ (k2_relat_1 @ X21)))
% 1.65/1.87          | ~ (v1_funct_1 @ X21)
% 1.65/1.87          | ~ (v1_relat_1 @ X21))),
% 1.65/1.87      inference('demod', [status(thm)], ['5', '6'])).
% 1.65/1.87  thf('8', plain,
% 1.65/1.87      (![X21 : $i]:
% 1.65/1.87         (~ (v2_funct_1 @ X21)
% 1.65/1.87          | ((k5_relat_1 @ (k2_funct_1 @ X21) @ X21)
% 1.65/1.87              = (k6_partfun1 @ (k2_relat_1 @ X21)))
% 1.65/1.87          | ~ (v1_funct_1 @ X21)
% 1.65/1.87          | ~ (v1_relat_1 @ X21))),
% 1.65/1.87      inference('demod', [status(thm)], ['5', '6'])).
% 1.65/1.87  thf('9', plain,
% 1.65/1.87      (![X21 : $i]:
% 1.65/1.87         (~ (v2_funct_1 @ X21)
% 1.65/1.87          | ((k5_relat_1 @ (k2_funct_1 @ X21) @ X21)
% 1.65/1.87              = (k6_partfun1 @ (k2_relat_1 @ X21)))
% 1.65/1.87          | ~ (v1_funct_1 @ X21)
% 1.65/1.87          | ~ (v1_relat_1 @ X21))),
% 1.65/1.87      inference('demod', [status(thm)], ['5', '6'])).
% 1.65/1.87  thf('10', plain,
% 1.65/1.87      (![X21 : $i]:
% 1.65/1.87         (~ (v2_funct_1 @ X21)
% 1.65/1.87          | ((k5_relat_1 @ (k2_funct_1 @ X21) @ X21)
% 1.65/1.87              = (k6_partfun1 @ (k2_relat_1 @ X21)))
% 1.65/1.87          | ~ (v1_funct_1 @ X21)
% 1.65/1.87          | ~ (v1_relat_1 @ X21))),
% 1.65/1.87      inference('demod', [status(thm)], ['5', '6'])).
% 1.65/1.87  thf('11', plain,
% 1.65/1.87      (![X21 : $i]:
% 1.65/1.87         (~ (v2_funct_1 @ X21)
% 1.65/1.87          | ((k5_relat_1 @ (k2_funct_1 @ X21) @ X21)
% 1.65/1.87              = (k6_partfun1 @ (k2_relat_1 @ X21)))
% 1.65/1.87          | ~ (v1_funct_1 @ X21)
% 1.65/1.87          | ~ (v1_relat_1 @ X21))),
% 1.65/1.87      inference('demod', [status(thm)], ['5', '6'])).
% 1.65/1.87  thf('12', plain,
% 1.65/1.87      (![X17 : $i]:
% 1.65/1.87         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 1.65/1.87          | ~ (v1_funct_1 @ X17)
% 1.65/1.87          | ~ (v1_relat_1 @ X17))),
% 1.65/1.87      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.65/1.87  thf(t55_funct_1, axiom,
% 1.65/1.87    (![A:$i]:
% 1.65/1.87     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.65/1.87       ( ( v2_funct_1 @ A ) =>
% 1.65/1.87         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.65/1.87           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.65/1.87  thf('13', plain,
% 1.65/1.87      (![X20 : $i]:
% 1.65/1.87         (~ (v2_funct_1 @ X20)
% 1.65/1.87          | ((k2_relat_1 @ X20) = (k1_relat_1 @ (k2_funct_1 @ X20)))
% 1.65/1.87          | ~ (v1_funct_1 @ X20)
% 1.65/1.87          | ~ (v1_relat_1 @ X20))),
% 1.65/1.87      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.65/1.87  thf('14', plain,
% 1.65/1.87      (![X17 : $i]:
% 1.65/1.87         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 1.65/1.87          | ~ (v1_funct_1 @ X17)
% 1.65/1.87          | ~ (v1_relat_1 @ X17))),
% 1.65/1.87      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.65/1.87  thf(t36_funct_2, conjecture,
% 1.65/1.87    (![A:$i,B:$i,C:$i]:
% 1.65/1.87     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.65/1.87         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.87       ( ![D:$i]:
% 1.65/1.87         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.65/1.87             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.65/1.87           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.65/1.87               ( r2_relset_1 @
% 1.65/1.87                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.65/1.87                 ( k6_partfun1 @ A ) ) & 
% 1.65/1.87               ( v2_funct_1 @ C ) ) =>
% 1.65/1.87             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.65/1.87               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.65/1.87  thf(zf_stmt_0, negated_conjecture,
% 1.65/1.87    (~( ![A:$i,B:$i,C:$i]:
% 1.65/1.87        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.65/1.87            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.87          ( ![D:$i]:
% 1.65/1.87            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.65/1.87                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.65/1.87              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.65/1.87                  ( r2_relset_1 @
% 1.65/1.87                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.65/1.87                    ( k6_partfun1 @ A ) ) & 
% 1.65/1.87                  ( v2_funct_1 @ C ) ) =>
% 1.65/1.87                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.65/1.87                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.65/1.87    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.65/1.87  thf('15', plain,
% 1.65/1.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf(redefinition_k2_relset_1, axiom,
% 1.65/1.87    (![A:$i,B:$i,C:$i]:
% 1.65/1.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.87       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.65/1.87  thf('16', plain,
% 1.65/1.87      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.65/1.87         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 1.65/1.87          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.65/1.87      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.65/1.87  thf('17', plain,
% 1.65/1.87      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.65/1.87      inference('sup-', [status(thm)], ['15', '16'])).
% 1.65/1.87  thf('18', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('19', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.65/1.87      inference('sup+', [status(thm)], ['17', '18'])).
% 1.65/1.87  thf('20', plain,
% 1.65/1.87      (![X17 : $i]:
% 1.65/1.87         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 1.65/1.87          | ~ (v1_funct_1 @ X17)
% 1.65/1.87          | ~ (v1_relat_1 @ X17))),
% 1.65/1.87      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.65/1.87  thf('21', plain,
% 1.65/1.87      (![X20 : $i]:
% 1.65/1.87         (~ (v2_funct_1 @ X20)
% 1.65/1.87          | ((k2_relat_1 @ X20) = (k1_relat_1 @ (k2_funct_1 @ X20)))
% 1.65/1.87          | ~ (v1_funct_1 @ X20)
% 1.65/1.87          | ~ (v1_relat_1 @ X20))),
% 1.65/1.87      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.65/1.87  thf(d10_xboole_0, axiom,
% 1.65/1.87    (![A:$i,B:$i]:
% 1.65/1.87     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.65/1.87  thf('22', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.65/1.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.65/1.87  thf('23', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.65/1.87      inference('simplify', [status(thm)], ['22'])).
% 1.65/1.87  thf(d18_relat_1, axiom,
% 1.65/1.87    (![A:$i,B:$i]:
% 1.65/1.87     ( ( v1_relat_1 @ B ) =>
% 1.65/1.87       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.65/1.87  thf('24', plain,
% 1.65/1.87      (![X3 : $i, X4 : $i]:
% 1.65/1.87         (~ (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.65/1.87          | (v4_relat_1 @ X3 @ X4)
% 1.65/1.87          | ~ (v1_relat_1 @ X3))),
% 1.65/1.87      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.65/1.87  thf('25', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 1.65/1.87      inference('sup-', [status(thm)], ['23', '24'])).
% 1.65/1.87  thf('26', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.65/1.87          | ~ (v1_relat_1 @ X0)
% 1.65/1.87          | ~ (v1_funct_1 @ X0)
% 1.65/1.87          | ~ (v2_funct_1 @ X0)
% 1.65/1.87          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.65/1.87      inference('sup+', [status(thm)], ['21', '25'])).
% 1.65/1.87  thf('27', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         (~ (v1_relat_1 @ X0)
% 1.65/1.87          | ~ (v1_funct_1 @ X0)
% 1.65/1.87          | ~ (v2_funct_1 @ X0)
% 1.65/1.87          | ~ (v1_funct_1 @ X0)
% 1.65/1.87          | ~ (v1_relat_1 @ X0)
% 1.65/1.87          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.65/1.87      inference('sup-', [status(thm)], ['20', '26'])).
% 1.65/1.87  thf('28', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.65/1.87          | ~ (v2_funct_1 @ X0)
% 1.65/1.87          | ~ (v1_funct_1 @ X0)
% 1.65/1.87          | ~ (v1_relat_1 @ X0))),
% 1.65/1.87      inference('simplify', [status(thm)], ['27'])).
% 1.65/1.87  thf('29', plain,
% 1.65/1.87      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 1.65/1.87        | ~ (v1_relat_1 @ sk_C)
% 1.65/1.87        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.87        | ~ (v2_funct_1 @ sk_C))),
% 1.65/1.87      inference('sup+', [status(thm)], ['19', '28'])).
% 1.65/1.87  thf('30', plain,
% 1.65/1.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf(cc1_relset_1, axiom,
% 1.65/1.87    (![A:$i,B:$i,C:$i]:
% 1.65/1.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.87       ( v1_relat_1 @ C ) ))).
% 1.65/1.87  thf('31', plain,
% 1.65/1.87      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.65/1.87         ((v1_relat_1 @ X22)
% 1.65/1.87          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.65/1.87      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.65/1.87  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.87      inference('sup-', [status(thm)], ['30', '31'])).
% 1.65/1.87  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('34', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('35', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 1.65/1.87      inference('demod', [status(thm)], ['29', '32', '33', '34'])).
% 1.65/1.87  thf('36', plain,
% 1.65/1.87      (![X3 : $i, X4 : $i]:
% 1.65/1.87         (~ (v4_relat_1 @ X3 @ X4)
% 1.65/1.87          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.65/1.87          | ~ (v1_relat_1 @ X3))),
% 1.65/1.87      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.65/1.87  thf('37', plain,
% 1.65/1.87      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.65/1.87        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.65/1.87      inference('sup-', [status(thm)], ['35', '36'])).
% 1.65/1.87  thf('38', plain,
% 1.65/1.87      ((~ (v1_relat_1 @ sk_C)
% 1.65/1.87        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.87        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.65/1.87      inference('sup-', [status(thm)], ['14', '37'])).
% 1.65/1.87  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.87      inference('sup-', [status(thm)], ['30', '31'])).
% 1.65/1.87  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('41', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 1.65/1.87      inference('demod', [status(thm)], ['38', '39', '40'])).
% 1.65/1.87  thf('42', plain,
% 1.65/1.87      (![X0 : $i, X2 : $i]:
% 1.65/1.87         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.65/1.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.65/1.87  thf('43', plain,
% 1.65/1.87      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.65/1.87        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.65/1.87      inference('sup-', [status(thm)], ['41', '42'])).
% 1.65/1.87  thf('44', plain,
% 1.65/1.87      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 1.65/1.87        | ~ (v1_relat_1 @ sk_C)
% 1.65/1.87        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.87        | ~ (v2_funct_1 @ sk_C)
% 1.65/1.87        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.65/1.87      inference('sup-', [status(thm)], ['13', '43'])).
% 1.65/1.87  thf('45', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.65/1.87      inference('sup+', [status(thm)], ['17', '18'])).
% 1.65/1.87  thf('46', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.65/1.87      inference('simplify', [status(thm)], ['22'])).
% 1.65/1.87  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.87      inference('sup-', [status(thm)], ['30', '31'])).
% 1.65/1.87  thf('48', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('49', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('50', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.65/1.87      inference('demod', [status(thm)], ['44', '45', '46', '47', '48', '49'])).
% 1.65/1.87  thf(t44_relat_1, axiom,
% 1.65/1.87    (![A:$i]:
% 1.65/1.87     ( ( v1_relat_1 @ A ) =>
% 1.65/1.87       ( ![B:$i]:
% 1.65/1.87         ( ( v1_relat_1 @ B ) =>
% 1.65/1.87           ( r1_tarski @
% 1.65/1.87             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 1.65/1.87  thf('51', plain,
% 1.65/1.87      (![X8 : $i, X9 : $i]:
% 1.65/1.87         (~ (v1_relat_1 @ X8)
% 1.65/1.87          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X9 @ X8)) @ 
% 1.65/1.87             (k1_relat_1 @ X9))
% 1.65/1.87          | ~ (v1_relat_1 @ X9))),
% 1.65/1.87      inference('cnf', [status(esa)], [t44_relat_1])).
% 1.65/1.87  thf('52', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         ((r1_tarski @ 
% 1.65/1.87           (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)) @ sk_B)
% 1.65/1.87          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.65/1.87          | ~ (v1_relat_1 @ X0))),
% 1.65/1.87      inference('sup+', [status(thm)], ['50', '51'])).
% 1.65/1.87  thf('53', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         (~ (v1_relat_1 @ sk_C)
% 1.65/1.87          | ~ (v1_funct_1 @ sk_C)
% 1.65/1.87          | ~ (v1_relat_1 @ X0)
% 1.65/1.87          | (r1_tarski @ 
% 1.65/1.87             (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)) @ sk_B))),
% 1.65/1.87      inference('sup-', [status(thm)], ['12', '52'])).
% 1.65/1.87  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.87      inference('sup-', [status(thm)], ['30', '31'])).
% 1.65/1.87  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('56', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         (~ (v1_relat_1 @ X0)
% 1.65/1.87          | (r1_tarski @ 
% 1.65/1.87             (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)) @ sk_B))),
% 1.65/1.87      inference('demod', [status(thm)], ['53', '54', '55'])).
% 1.65/1.87  thf('57', plain,
% 1.65/1.87      (![X3 : $i, X4 : $i]:
% 1.65/1.87         (~ (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.65/1.87          | (v4_relat_1 @ X3 @ X4)
% 1.65/1.87          | ~ (v1_relat_1 @ X3))),
% 1.65/1.87      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.65/1.87  thf('58', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         (~ (v1_relat_1 @ X0)
% 1.65/1.87          | ~ (v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))
% 1.65/1.87          | (v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0) @ sk_B))),
% 1.65/1.87      inference('sup-', [status(thm)], ['56', '57'])).
% 1.65/1.87  thf('59', plain,
% 1.65/1.87      ((~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.65/1.87        | ~ (v1_relat_1 @ sk_C)
% 1.65/1.87        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.87        | ~ (v2_funct_1 @ sk_C)
% 1.65/1.87        | (v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) @ sk_B)
% 1.65/1.87        | ~ (v1_relat_1 @ sk_C))),
% 1.65/1.87      inference('sup-', [status(thm)], ['11', '58'])).
% 1.65/1.87  thf('60', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.65/1.87      inference('sup+', [status(thm)], ['17', '18'])).
% 1.65/1.87  thf(t29_relset_1, axiom,
% 1.65/1.87    (![A:$i]:
% 1.65/1.87     ( m1_subset_1 @
% 1.65/1.87       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.65/1.87  thf('61', plain,
% 1.65/1.87      (![X35 : $i]:
% 1.65/1.87         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 1.65/1.87          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 1.65/1.87      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.65/1.87  thf('62', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 1.65/1.87      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.65/1.87  thf('63', plain,
% 1.65/1.87      (![X35 : $i]:
% 1.65/1.87         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 1.65/1.87          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 1.65/1.87      inference('demod', [status(thm)], ['61', '62'])).
% 1.65/1.87  thf('64', plain,
% 1.65/1.87      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.65/1.87         ((v1_relat_1 @ X22)
% 1.65/1.87          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.65/1.87      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.65/1.87  thf('65', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.65/1.87      inference('sup-', [status(thm)], ['63', '64'])).
% 1.65/1.87  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.87      inference('sup-', [status(thm)], ['30', '31'])).
% 1.65/1.87  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('68', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('69', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.87      inference('sup-', [status(thm)], ['30', '31'])).
% 1.65/1.87  thf('70', plain,
% 1.65/1.87      ((v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) @ sk_B)),
% 1.65/1.87      inference('demod', [status(thm)],
% 1.65/1.87                ['59', '60', '65', '66', '67', '68', '69'])).
% 1.65/1.87  thf('71', plain,
% 1.65/1.87      (![X3 : $i, X4 : $i]:
% 1.65/1.87         (~ (v4_relat_1 @ X3 @ X4)
% 1.65/1.87          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.65/1.87          | ~ (v1_relat_1 @ X3))),
% 1.65/1.87      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.65/1.87  thf('72', plain,
% 1.65/1.87      ((~ (v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.65/1.87        | (r1_tarski @ 
% 1.65/1.87           (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)) @ sk_B))),
% 1.65/1.87      inference('sup-', [status(thm)], ['70', '71'])).
% 1.65/1.87  thf('73', plain,
% 1.65/1.87      ((~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.65/1.87        | ~ (v1_relat_1 @ sk_C)
% 1.65/1.87        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.87        | ~ (v2_funct_1 @ sk_C)
% 1.65/1.87        | (r1_tarski @ 
% 1.65/1.87           (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)) @ sk_B))),
% 1.65/1.87      inference('sup-', [status(thm)], ['10', '72'])).
% 1.65/1.87  thf('74', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.65/1.87      inference('sup+', [status(thm)], ['17', '18'])).
% 1.65/1.87  thf('75', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.65/1.87      inference('sup-', [status(thm)], ['63', '64'])).
% 1.65/1.87  thf('76', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.87      inference('sup-', [status(thm)], ['30', '31'])).
% 1.65/1.87  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('78', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('79', plain,
% 1.65/1.87      ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)) @ 
% 1.65/1.87        sk_B)),
% 1.65/1.87      inference('demod', [status(thm)], ['73', '74', '75', '76', '77', '78'])).
% 1.65/1.87  thf('80', plain,
% 1.65/1.87      (![X0 : $i, X2 : $i]:
% 1.65/1.87         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.65/1.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.65/1.87  thf('81', plain,
% 1.65/1.87      ((~ (r1_tarski @ sk_B @ 
% 1.65/1.87           (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))
% 1.65/1.87        | ((sk_B) = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))))),
% 1.65/1.87      inference('sup-', [status(thm)], ['79', '80'])).
% 1.65/1.87  thf('82', plain,
% 1.65/1.87      ((~ (r1_tarski @ sk_B @ 
% 1.65/1.87           (k1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C))))
% 1.65/1.87        | ~ (v1_relat_1 @ sk_C)
% 1.65/1.87        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.87        | ~ (v2_funct_1 @ sk_C)
% 1.65/1.87        | ((sk_B) = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))))),
% 1.65/1.87      inference('sup-', [status(thm)], ['9', '81'])).
% 1.65/1.87  thf('83', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.65/1.87      inference('sup+', [status(thm)], ['17', '18'])).
% 1.65/1.87  thf(t71_relat_1, axiom,
% 1.65/1.87    (![A:$i]:
% 1.65/1.87     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.65/1.87       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.65/1.87  thf('84', plain, (![X13 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 1.65/1.87      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.65/1.87  thf('85', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 1.65/1.87      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.65/1.87  thf('86', plain, (![X13 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X13)) = (X13))),
% 1.65/1.87      inference('demod', [status(thm)], ['84', '85'])).
% 1.65/1.87  thf('87', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.65/1.87      inference('simplify', [status(thm)], ['22'])).
% 1.65/1.87  thf('88', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.87      inference('sup-', [status(thm)], ['30', '31'])).
% 1.65/1.87  thf('89', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('90', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('91', plain,
% 1.65/1.87      (((sk_B) = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 1.65/1.87      inference('demod', [status(thm)],
% 1.65/1.87                ['82', '83', '86', '87', '88', '89', '90'])).
% 1.65/1.87  thf(t78_relat_1, axiom,
% 1.65/1.87    (![A:$i]:
% 1.65/1.87     ( ( v1_relat_1 @ A ) =>
% 1.65/1.87       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 1.65/1.87  thf('92', plain,
% 1.65/1.87      (![X15 : $i]:
% 1.65/1.87         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X15)) @ X15) = (X15))
% 1.65/1.87          | ~ (v1_relat_1 @ X15))),
% 1.65/1.87      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.65/1.87  thf('93', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 1.65/1.87      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.65/1.87  thf('94', plain,
% 1.65/1.87      (![X15 : $i]:
% 1.65/1.87         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X15)) @ X15) = (X15))
% 1.65/1.87          | ~ (v1_relat_1 @ X15))),
% 1.65/1.87      inference('demod', [status(thm)], ['92', '93'])).
% 1.65/1.87  thf('95', plain,
% 1.65/1.87      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.65/1.87          (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.65/1.87          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.65/1.87        | ~ (v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 1.65/1.87      inference('sup+', [status(thm)], ['91', '94'])).
% 1.65/1.87  thf('96', plain,
% 1.65/1.87      ((~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.65/1.87        | ~ (v1_relat_1 @ sk_C)
% 1.65/1.87        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.87        | ~ (v2_funct_1 @ sk_C)
% 1.65/1.87        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.65/1.87            (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.65/1.87            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 1.65/1.87      inference('sup-', [status(thm)], ['8', '95'])).
% 1.65/1.87  thf('97', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.65/1.87      inference('sup+', [status(thm)], ['17', '18'])).
% 1.65/1.87  thf('98', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.65/1.87      inference('sup-', [status(thm)], ['63', '64'])).
% 1.65/1.87  thf('99', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.87      inference('sup-', [status(thm)], ['30', '31'])).
% 1.65/1.87  thf('100', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('101', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('102', plain,
% 1.65/1.87      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.65/1.87         (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.65/1.87         = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))),
% 1.65/1.87      inference('demod', [status(thm)], ['96', '97', '98', '99', '100', '101'])).
% 1.65/1.87  thf('103', plain,
% 1.65/1.87      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.65/1.87          (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.65/1.87          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.65/1.87        | ~ (v1_relat_1 @ sk_C)
% 1.65/1.87        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.87        | ~ (v2_funct_1 @ sk_C))),
% 1.65/1.87      inference('sup+', [status(thm)], ['7', '102'])).
% 1.65/1.87  thf('104', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.65/1.87      inference('sup+', [status(thm)], ['17', '18'])).
% 1.65/1.87  thf('105', plain,
% 1.65/1.87      (![X13 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X13)) = (X13))),
% 1.65/1.87      inference('demod', [status(thm)], ['84', '85'])).
% 1.65/1.87  thf('106', plain,
% 1.65/1.87      (![X15 : $i]:
% 1.65/1.87         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X15)) @ X15) = (X15))
% 1.65/1.87          | ~ (v1_relat_1 @ X15))),
% 1.65/1.87      inference('demod', [status(thm)], ['92', '93'])).
% 1.65/1.87  thf('107', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.65/1.87            = (k6_partfun1 @ X0))
% 1.65/1.87          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.65/1.87      inference('sup+', [status(thm)], ['105', '106'])).
% 1.65/1.87  thf('108', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.65/1.87      inference('sup-', [status(thm)], ['63', '64'])).
% 1.65/1.87  thf('109', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.65/1.87           = (k6_partfun1 @ X0))),
% 1.65/1.87      inference('demod', [status(thm)], ['107', '108'])).
% 1.65/1.87  thf('110', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.87      inference('sup-', [status(thm)], ['30', '31'])).
% 1.65/1.87  thf('111', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('112', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('113', plain,
% 1.65/1.87      (((k6_partfun1 @ sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))),
% 1.65/1.87      inference('demod', [status(thm)],
% 1.65/1.87                ['103', '104', '109', '110', '111', '112'])).
% 1.65/1.87  thf(t55_relat_1, axiom,
% 1.65/1.87    (![A:$i]:
% 1.65/1.87     ( ( v1_relat_1 @ A ) =>
% 1.65/1.87       ( ![B:$i]:
% 1.65/1.87         ( ( v1_relat_1 @ B ) =>
% 1.65/1.87           ( ![C:$i]:
% 1.65/1.87             ( ( v1_relat_1 @ C ) =>
% 1.65/1.87               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.65/1.87                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.65/1.87  thf('114', plain,
% 1.65/1.87      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.65/1.87         (~ (v1_relat_1 @ X10)
% 1.65/1.87          | ((k5_relat_1 @ (k5_relat_1 @ X11 @ X10) @ X12)
% 1.65/1.87              = (k5_relat_1 @ X11 @ (k5_relat_1 @ X10 @ X12)))
% 1.65/1.87          | ~ (v1_relat_1 @ X12)
% 1.65/1.87          | ~ (v1_relat_1 @ X11))),
% 1.65/1.87      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.65/1.87  thf('115', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.65/1.87            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.65/1.87          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.65/1.87          | ~ (v1_relat_1 @ X0)
% 1.65/1.87          | ~ (v1_relat_1 @ sk_C))),
% 1.65/1.87      inference('sup+', [status(thm)], ['113', '114'])).
% 1.65/1.87  thf('116', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.87      inference('sup-', [status(thm)], ['30', '31'])).
% 1.65/1.87  thf('117', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.65/1.87            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.65/1.87          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.65/1.87          | ~ (v1_relat_1 @ X0))),
% 1.65/1.87      inference('demod', [status(thm)], ['115', '116'])).
% 1.65/1.87  thf('118', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         (~ (v1_relat_1 @ sk_C)
% 1.65/1.87          | ~ (v1_funct_1 @ sk_C)
% 1.65/1.87          | ~ (v1_relat_1 @ X0)
% 1.65/1.87          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.65/1.87              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.65/1.87      inference('sup-', [status(thm)], ['4', '117'])).
% 1.65/1.87  thf('119', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.87      inference('sup-', [status(thm)], ['30', '31'])).
% 1.65/1.87  thf('120', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('121', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         (~ (v1_relat_1 @ X0)
% 1.65/1.87          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.65/1.87              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.65/1.87      inference('demod', [status(thm)], ['118', '119', '120'])).
% 1.65/1.87  thf('122', plain,
% 1.65/1.87      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.65/1.87          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 1.65/1.87             (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 1.65/1.87        | ~ (v1_relat_1 @ sk_C)
% 1.65/1.87        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.87        | ~ (v2_funct_1 @ sk_C)
% 1.65/1.87        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.65/1.87      inference('sup+', [status(thm)], ['3', '121'])).
% 1.65/1.87  thf('123', plain,
% 1.65/1.87      (![X17 : $i]:
% 1.65/1.87         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 1.65/1.87          | ~ (v1_funct_1 @ X17)
% 1.65/1.87          | ~ (v1_relat_1 @ X17))),
% 1.65/1.87      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.65/1.87  thf('124', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.65/1.87      inference('demod', [status(thm)], ['44', '45', '46', '47', '48', '49'])).
% 1.65/1.87  thf('125', plain,
% 1.65/1.87      (![X15 : $i]:
% 1.65/1.87         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X15)) @ X15) = (X15))
% 1.65/1.87          | ~ (v1_relat_1 @ X15))),
% 1.65/1.87      inference('demod', [status(thm)], ['92', '93'])).
% 1.65/1.87  thf('126', plain,
% 1.65/1.87      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.65/1.87          = (k2_funct_1 @ sk_C))
% 1.65/1.87        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.65/1.87      inference('sup+', [status(thm)], ['124', '125'])).
% 1.65/1.87  thf('127', plain,
% 1.65/1.87      ((~ (v1_relat_1 @ sk_C)
% 1.65/1.87        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.87        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.65/1.87            = (k2_funct_1 @ sk_C)))),
% 1.65/1.87      inference('sup-', [status(thm)], ['123', '126'])).
% 1.65/1.87  thf('128', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.87      inference('sup-', [status(thm)], ['30', '31'])).
% 1.65/1.87  thf('129', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('130', plain,
% 1.65/1.87      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.65/1.87         = (k2_funct_1 @ sk_C))),
% 1.65/1.87      inference('demod', [status(thm)], ['127', '128', '129'])).
% 1.65/1.87  thf('131', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.87      inference('sup-', [status(thm)], ['30', '31'])).
% 1.65/1.87  thf('132', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('133', plain, ((v2_funct_1 @ sk_C)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('134', plain,
% 1.65/1.87      ((((k2_funct_1 @ sk_C)
% 1.65/1.87          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 1.65/1.87             (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 1.65/1.87        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.65/1.87      inference('demod', [status(thm)], ['122', '130', '131', '132', '133'])).
% 1.65/1.87  thf('135', plain,
% 1.65/1.87      ((~ (v1_relat_1 @ sk_C)
% 1.65/1.87        | ~ (v1_funct_1 @ sk_C)
% 1.65/1.87        | ((k2_funct_1 @ sk_C)
% 1.65/1.87            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 1.65/1.87               (k6_partfun1 @ (k1_relat_1 @ sk_C)))))),
% 1.65/1.87      inference('sup-', [status(thm)], ['0', '134'])).
% 1.65/1.87  thf('136', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.87      inference('sup-', [status(thm)], ['30', '31'])).
% 1.65/1.87  thf('137', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('138', plain,
% 1.65/1.87      (((k2_funct_1 @ sk_C)
% 1.65/1.87         = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 1.65/1.87            (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 1.65/1.87      inference('demod', [status(thm)], ['135', '136', '137'])).
% 1.65/1.87  thf('139', plain,
% 1.65/1.87      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('140', plain,
% 1.65/1.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf(redefinition_k1_partfun1, axiom,
% 1.65/1.87    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.65/1.87     ( ( ( v1_funct_1 @ E ) & 
% 1.65/1.87         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.65/1.87         ( v1_funct_1 @ F ) & 
% 1.65/1.87         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.65/1.87       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.65/1.87  thf('141', plain,
% 1.65/1.87      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 1.65/1.87         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 1.65/1.87          | ~ (v1_funct_1 @ X42)
% 1.65/1.87          | ~ (v1_funct_1 @ X45)
% 1.65/1.87          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 1.65/1.87          | ((k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45)
% 1.65/1.87              = (k5_relat_1 @ X42 @ X45)))),
% 1.65/1.87      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.65/1.87  thf('142', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.87         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.65/1.87            = (k5_relat_1 @ sk_C @ X0))
% 1.65/1.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.65/1.87          | ~ (v1_funct_1 @ X0)
% 1.65/1.87          | ~ (v1_funct_1 @ sk_C))),
% 1.65/1.87      inference('sup-', [status(thm)], ['140', '141'])).
% 1.65/1.87  thf('143', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('144', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.87         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.65/1.87            = (k5_relat_1 @ sk_C @ X0))
% 1.65/1.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.65/1.87          | ~ (v1_funct_1 @ X0))),
% 1.65/1.87      inference('demod', [status(thm)], ['142', '143'])).
% 1.65/1.87  thf('145', plain,
% 1.65/1.87      ((~ (v1_funct_1 @ sk_D)
% 1.65/1.87        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.65/1.87            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.65/1.87      inference('sup-', [status(thm)], ['139', '144'])).
% 1.65/1.87  thf('146', plain, ((v1_funct_1 @ sk_D)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('147', plain,
% 1.65/1.87      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.65/1.87        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.65/1.87        (k6_partfun1 @ sk_A))),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('148', plain,
% 1.65/1.87      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('149', plain,
% 1.65/1.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf(dt_k1_partfun1, axiom,
% 1.65/1.87    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.65/1.87     ( ( ( v1_funct_1 @ E ) & 
% 1.65/1.87         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.65/1.87         ( v1_funct_1 @ F ) & 
% 1.65/1.87         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.65/1.87       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.65/1.87         ( m1_subset_1 @
% 1.65/1.87           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.65/1.87           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.65/1.87  thf('150', plain,
% 1.65/1.87      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.65/1.87         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 1.65/1.87          | ~ (v1_funct_1 @ X36)
% 1.65/1.87          | ~ (v1_funct_1 @ X39)
% 1.65/1.87          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 1.65/1.87          | (m1_subset_1 @ (k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39) @ 
% 1.65/1.87             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X41))))),
% 1.65/1.87      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.65/1.87  thf('151', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.87         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.65/1.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.65/1.87          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.65/1.87          | ~ (v1_funct_1 @ X1)
% 1.65/1.87          | ~ (v1_funct_1 @ sk_C))),
% 1.65/1.87      inference('sup-', [status(thm)], ['149', '150'])).
% 1.65/1.87  thf('152', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('153', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.87         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.65/1.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.65/1.87          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.65/1.87          | ~ (v1_funct_1 @ X1))),
% 1.65/1.87      inference('demod', [status(thm)], ['151', '152'])).
% 1.65/1.87  thf('154', plain,
% 1.65/1.87      ((~ (v1_funct_1 @ sk_D)
% 1.65/1.87        | (m1_subset_1 @ 
% 1.65/1.87           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.65/1.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.65/1.87      inference('sup-', [status(thm)], ['148', '153'])).
% 1.65/1.87  thf('155', plain, ((v1_funct_1 @ sk_D)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('156', plain,
% 1.65/1.87      ((m1_subset_1 @ 
% 1.65/1.87        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.65/1.87        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.65/1.87      inference('demod', [status(thm)], ['154', '155'])).
% 1.65/1.87  thf(redefinition_r2_relset_1, axiom,
% 1.65/1.87    (![A:$i,B:$i,C:$i,D:$i]:
% 1.65/1.87     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.65/1.87         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.65/1.87       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.65/1.87  thf('157', plain,
% 1.65/1.87      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.65/1.87         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.65/1.87          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.65/1.87          | ((X31) = (X34))
% 1.65/1.87          | ~ (r2_relset_1 @ X32 @ X33 @ X31 @ X34))),
% 1.65/1.87      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.65/1.87  thf('158', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.65/1.87             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 1.65/1.87          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 1.65/1.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.65/1.87      inference('sup-', [status(thm)], ['156', '157'])).
% 1.65/1.87  thf('159', plain,
% 1.65/1.87      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.65/1.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.65/1.87        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.65/1.87            = (k6_partfun1 @ sk_A)))),
% 1.65/1.87      inference('sup-', [status(thm)], ['147', '158'])).
% 1.65/1.87  thf('160', plain,
% 1.65/1.87      (![X35 : $i]:
% 1.65/1.87         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 1.65/1.87          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 1.65/1.87      inference('demod', [status(thm)], ['61', '62'])).
% 1.65/1.87  thf('161', plain,
% 1.65/1.87      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.65/1.87         = (k6_partfun1 @ sk_A))),
% 1.65/1.87      inference('demod', [status(thm)], ['159', '160'])).
% 1.65/1.87  thf('162', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.65/1.87      inference('demod', [status(thm)], ['145', '146', '161'])).
% 1.65/1.87  thf('163', plain,
% 1.65/1.87      (![X8 : $i, X9 : $i]:
% 1.65/1.87         (~ (v1_relat_1 @ X8)
% 1.65/1.87          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X9 @ X8)) @ 
% 1.65/1.87             (k1_relat_1 @ X9))
% 1.65/1.87          | ~ (v1_relat_1 @ X9))),
% 1.65/1.87      inference('cnf', [status(esa)], [t44_relat_1])).
% 1.65/1.87  thf('164', plain,
% 1.65/1.87      (![X0 : $i, X2 : $i]:
% 1.65/1.87         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.65/1.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.65/1.87  thf('165', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         (~ (v1_relat_1 @ X0)
% 1.65/1.87          | ~ (v1_relat_1 @ X1)
% 1.65/1.87          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ 
% 1.65/1.87               (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 1.65/1.87          | ((k1_relat_1 @ X0) = (k1_relat_1 @ (k5_relat_1 @ X0 @ X1))))),
% 1.65/1.87      inference('sup-', [status(thm)], ['163', '164'])).
% 1.65/1.87  thf('166', plain,
% 1.65/1.87      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ 
% 1.65/1.87           (k1_relat_1 @ (k6_partfun1 @ sk_A)))
% 1.65/1.87        | ((k1_relat_1 @ sk_C) = (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 1.65/1.87        | ~ (v1_relat_1 @ sk_D)
% 1.65/1.87        | ~ (v1_relat_1 @ sk_C))),
% 1.65/1.87      inference('sup-', [status(thm)], ['162', '165'])).
% 1.65/1.87  thf('167', plain,
% 1.65/1.87      (![X13 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X13)) = (X13))),
% 1.65/1.87      inference('demod', [status(thm)], ['84', '85'])).
% 1.65/1.87  thf('168', plain,
% 1.65/1.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf(cc2_relset_1, axiom,
% 1.65/1.87    (![A:$i,B:$i,C:$i]:
% 1.65/1.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.65/1.87       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.65/1.87  thf('169', plain,
% 1.65/1.87      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.65/1.87         ((v4_relat_1 @ X25 @ X26)
% 1.65/1.87          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.65/1.87      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.65/1.87  thf('170', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 1.65/1.87      inference('sup-', [status(thm)], ['168', '169'])).
% 1.65/1.87  thf('171', plain,
% 1.65/1.87      (![X3 : $i, X4 : $i]:
% 1.65/1.87         (~ (v4_relat_1 @ X3 @ X4)
% 1.65/1.87          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.65/1.87          | ~ (v1_relat_1 @ X3))),
% 1.65/1.87      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.65/1.87  thf('172', plain,
% 1.65/1.87      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 1.65/1.87      inference('sup-', [status(thm)], ['170', '171'])).
% 1.65/1.87  thf('173', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.87      inference('sup-', [status(thm)], ['30', '31'])).
% 1.65/1.87  thf('174', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 1.65/1.87      inference('demod', [status(thm)], ['172', '173'])).
% 1.65/1.87  thf('175', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.65/1.87      inference('demod', [status(thm)], ['145', '146', '161'])).
% 1.65/1.87  thf('176', plain,
% 1.65/1.87      (![X13 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X13)) = (X13))),
% 1.65/1.87      inference('demod', [status(thm)], ['84', '85'])).
% 1.65/1.87  thf('177', plain,
% 1.65/1.87      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('178', plain,
% 1.65/1.87      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.65/1.87         ((v1_relat_1 @ X22)
% 1.65/1.87          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.65/1.87      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.65/1.87  thf('179', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.87      inference('sup-', [status(thm)], ['177', '178'])).
% 1.65/1.87  thf('180', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.87      inference('sup-', [status(thm)], ['30', '31'])).
% 1.65/1.87  thf('181', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 1.65/1.87      inference('demod', [status(thm)],
% 1.65/1.87                ['166', '167', '174', '175', '176', '179', '180'])).
% 1.65/1.87  thf('182', plain,
% 1.65/1.87      (((k2_funct_1 @ sk_C)
% 1.65/1.87         = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))),
% 1.65/1.87      inference('demod', [status(thm)], ['138', '181'])).
% 1.65/1.87  thf('183', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.65/1.87      inference('demod', [status(thm)], ['145', '146', '161'])).
% 1.65/1.87  thf('184', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         (~ (v1_relat_1 @ X0)
% 1.65/1.87          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.65/1.87              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.65/1.87      inference('demod', [status(thm)], ['118', '119', '120'])).
% 1.65/1.87  thf('185', plain,
% 1.65/1.87      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.65/1.87          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 1.65/1.87        | ~ (v1_relat_1 @ sk_D))),
% 1.65/1.87      inference('sup+', [status(thm)], ['183', '184'])).
% 1.65/1.87  thf('186', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.87      inference('sup-', [status(thm)], ['177', '178'])).
% 1.65/1.87  thf('187', plain,
% 1.65/1.87      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.65/1.87         = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))),
% 1.65/1.87      inference('demod', [status(thm)], ['185', '186'])).
% 1.65/1.87  thf(t169_relat_1, axiom,
% 1.65/1.87    (![A:$i]:
% 1.65/1.87     ( ( v1_relat_1 @ A ) =>
% 1.65/1.87       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 1.65/1.87  thf('188', plain,
% 1.65/1.87      (![X5 : $i]:
% 1.65/1.87         (((k10_relat_1 @ X5 @ (k2_relat_1 @ X5)) = (k1_relat_1 @ X5))
% 1.65/1.87          | ~ (v1_relat_1 @ X5))),
% 1.65/1.87      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.65/1.87  thf(t182_relat_1, axiom,
% 1.65/1.87    (![A:$i]:
% 1.65/1.87     ( ( v1_relat_1 @ A ) =>
% 1.65/1.87       ( ![B:$i]:
% 1.65/1.87         ( ( v1_relat_1 @ B ) =>
% 1.65/1.87           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.65/1.87             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 1.65/1.87  thf('189', plain,
% 1.65/1.87      (![X6 : $i, X7 : $i]:
% 1.65/1.87         (~ (v1_relat_1 @ X6)
% 1.65/1.87          | ((k1_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 1.65/1.87              = (k10_relat_1 @ X7 @ (k1_relat_1 @ X6)))
% 1.65/1.87          | ~ (v1_relat_1 @ X7))),
% 1.65/1.87      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.65/1.87  thf(t80_relat_1, axiom,
% 1.65/1.87    (![A:$i]:
% 1.65/1.87     ( ( v1_relat_1 @ A ) =>
% 1.65/1.87       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 1.65/1.87  thf('190', plain,
% 1.65/1.87      (![X16 : $i]:
% 1.65/1.87         (((k5_relat_1 @ X16 @ (k6_relat_1 @ (k2_relat_1 @ X16))) = (X16))
% 1.65/1.87          | ~ (v1_relat_1 @ X16))),
% 1.65/1.87      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.65/1.87  thf('191', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 1.65/1.87      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.65/1.87  thf('192', plain,
% 1.65/1.87      (![X16 : $i]:
% 1.65/1.87         (((k5_relat_1 @ X16 @ (k6_partfun1 @ (k2_relat_1 @ X16))) = (X16))
% 1.65/1.87          | ~ (v1_relat_1 @ X16))),
% 1.65/1.87      inference('demod', [status(thm)], ['190', '191'])).
% 1.65/1.87  thf('193', plain,
% 1.65/1.87      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('194', plain,
% 1.65/1.87      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.65/1.87         ((v4_relat_1 @ X25 @ X26)
% 1.65/1.87          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.65/1.87      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.65/1.87  thf('195', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 1.65/1.87      inference('sup-', [status(thm)], ['193', '194'])).
% 1.65/1.87  thf('196', plain,
% 1.65/1.87      (![X3 : $i, X4 : $i]:
% 1.65/1.87         (~ (v4_relat_1 @ X3 @ X4)
% 1.65/1.87          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.65/1.87          | ~ (v1_relat_1 @ X3))),
% 1.65/1.87      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.65/1.87  thf('197', plain,
% 1.65/1.87      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 1.65/1.87      inference('sup-', [status(thm)], ['195', '196'])).
% 1.65/1.87  thf('198', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.87      inference('sup-', [status(thm)], ['177', '178'])).
% 1.65/1.87  thf('199', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 1.65/1.87      inference('demod', [status(thm)], ['197', '198'])).
% 1.65/1.87  thf('200', plain,
% 1.65/1.87      (![X5 : $i]:
% 1.65/1.87         (((k10_relat_1 @ X5 @ (k2_relat_1 @ X5)) = (k1_relat_1 @ X5))
% 1.65/1.87          | ~ (v1_relat_1 @ X5))),
% 1.65/1.87      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.65/1.87  thf('201', plain,
% 1.65/1.87      (![X16 : $i]:
% 1.65/1.87         (((k5_relat_1 @ X16 @ (k6_partfun1 @ (k2_relat_1 @ X16))) = (X16))
% 1.65/1.87          | ~ (v1_relat_1 @ X16))),
% 1.65/1.87      inference('demod', [status(thm)], ['190', '191'])).
% 1.65/1.87  thf('202', plain,
% 1.65/1.87      (![X13 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X13)) = (X13))),
% 1.65/1.87      inference('demod', [status(thm)], ['84', '85'])).
% 1.65/1.87  thf('203', plain,
% 1.65/1.87      (![X6 : $i, X7 : $i]:
% 1.65/1.87         (~ (v1_relat_1 @ X6)
% 1.65/1.87          | ((k1_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 1.65/1.87              = (k10_relat_1 @ X7 @ (k1_relat_1 @ X6)))
% 1.65/1.87          | ~ (v1_relat_1 @ X7))),
% 1.65/1.87      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.65/1.87  thf('204', plain,
% 1.65/1.87      (![X3 : $i, X4 : $i]:
% 1.65/1.87         (~ (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.65/1.87          | (v4_relat_1 @ X3 @ X4)
% 1.65/1.87          | ~ (v1_relat_1 @ X3))),
% 1.65/1.87      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.65/1.87  thf('205', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.87         (~ (r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ X2)
% 1.65/1.87          | ~ (v1_relat_1 @ X1)
% 1.65/1.87          | ~ (v1_relat_1 @ X0)
% 1.65/1.87          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.65/1.87          | (v4_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2))),
% 1.65/1.87      inference('sup-', [status(thm)], ['203', '204'])).
% 1.65/1.87  thf('206', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.87         (~ (r1_tarski @ (k10_relat_1 @ X2 @ X0) @ X1)
% 1.65/1.87          | (v4_relat_1 @ (k5_relat_1 @ X2 @ (k6_partfun1 @ X0)) @ X1)
% 1.65/1.87          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ (k6_partfun1 @ X0)))
% 1.65/1.87          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.65/1.87          | ~ (v1_relat_1 @ X2))),
% 1.65/1.87      inference('sup-', [status(thm)], ['202', '205'])).
% 1.65/1.87  thf('207', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.65/1.87      inference('sup-', [status(thm)], ['63', '64'])).
% 1.65/1.87  thf('208', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.65/1.87         (~ (r1_tarski @ (k10_relat_1 @ X2 @ X0) @ X1)
% 1.65/1.87          | (v4_relat_1 @ (k5_relat_1 @ X2 @ (k6_partfun1 @ X0)) @ X1)
% 1.65/1.87          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ (k6_partfun1 @ X0)))
% 1.65/1.87          | ~ (v1_relat_1 @ X2))),
% 1.65/1.87      inference('demod', [status(thm)], ['206', '207'])).
% 1.65/1.87  thf('209', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         (~ (v1_relat_1 @ X0)
% 1.65/1.87          | ~ (v1_relat_1 @ X0)
% 1.65/1.87          | ~ (v1_relat_1 @ X0)
% 1.65/1.87          | (v4_relat_1 @ 
% 1.65/1.87             (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) @ X1)
% 1.65/1.87          | ~ (r1_tarski @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) @ X1))),
% 1.65/1.87      inference('sup-', [status(thm)], ['201', '208'])).
% 1.65/1.87  thf('210', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         (~ (r1_tarski @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) @ X1)
% 1.65/1.87          | (v4_relat_1 @ 
% 1.65/1.87             (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) @ X1)
% 1.65/1.87          | ~ (v1_relat_1 @ X0))),
% 1.65/1.87      inference('simplify', [status(thm)], ['209'])).
% 1.65/1.87  thf('211', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.65/1.87          | ~ (v1_relat_1 @ X0)
% 1.65/1.87          | ~ (v1_relat_1 @ X0)
% 1.65/1.87          | (v4_relat_1 @ 
% 1.65/1.87             (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) @ X1))),
% 1.65/1.87      inference('sup-', [status(thm)], ['200', '210'])).
% 1.65/1.87  thf('212', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         ((v4_relat_1 @ 
% 1.65/1.87           (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))) @ X1)
% 1.65/1.87          | ~ (v1_relat_1 @ X0)
% 1.65/1.87          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ X1))),
% 1.65/1.87      inference('simplify', [status(thm)], ['211'])).
% 1.65/1.87  thf('213', plain,
% 1.65/1.87      ((~ (v1_relat_1 @ sk_D)
% 1.65/1.87        | (v4_relat_1 @ 
% 1.65/1.87           (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))) @ sk_B))),
% 1.65/1.87      inference('sup-', [status(thm)], ['199', '212'])).
% 1.65/1.87  thf('214', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.87      inference('sup-', [status(thm)], ['177', '178'])).
% 1.65/1.87  thf('215', plain,
% 1.65/1.87      ((v4_relat_1 @ 
% 1.65/1.87        (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))) @ sk_B)),
% 1.65/1.87      inference('demod', [status(thm)], ['213', '214'])).
% 1.65/1.87  thf('216', plain,
% 1.65/1.87      (![X3 : $i, X4 : $i]:
% 1.65/1.87         (~ (v4_relat_1 @ X3 @ X4)
% 1.65/1.87          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.65/1.87          | ~ (v1_relat_1 @ X3))),
% 1.65/1.87      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.65/1.87  thf('217', plain,
% 1.65/1.87      ((~ (v1_relat_1 @ 
% 1.65/1.87           (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))
% 1.65/1.87        | (r1_tarski @ 
% 1.65/1.87           (k1_relat_1 @ 
% 1.65/1.87            (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D)))) @ 
% 1.65/1.87           sk_B))),
% 1.65/1.87      inference('sup-', [status(thm)], ['215', '216'])).
% 1.65/1.87  thf('218', plain,
% 1.65/1.87      ((~ (v1_relat_1 @ sk_D)
% 1.65/1.87        | ~ (v1_relat_1 @ sk_D)
% 1.65/1.87        | (r1_tarski @ 
% 1.65/1.87           (k1_relat_1 @ 
% 1.65/1.87            (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D)))) @ 
% 1.65/1.87           sk_B))),
% 1.65/1.87      inference('sup-', [status(thm)], ['192', '217'])).
% 1.65/1.87  thf('219', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.87      inference('sup-', [status(thm)], ['177', '178'])).
% 1.65/1.87  thf('220', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.87      inference('sup-', [status(thm)], ['177', '178'])).
% 1.65/1.87  thf('221', plain,
% 1.65/1.87      ((r1_tarski @ 
% 1.65/1.87        (k1_relat_1 @ (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D)))) @ 
% 1.65/1.87        sk_B)),
% 1.65/1.87      inference('demod', [status(thm)], ['218', '219', '220'])).
% 1.65/1.87  thf('222', plain,
% 1.65/1.87      (((r1_tarski @ 
% 1.65/1.87         (k10_relat_1 @ sk_D @ 
% 1.65/1.87          (k1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_D)))) @ 
% 1.65/1.87         sk_B)
% 1.65/1.87        | ~ (v1_relat_1 @ sk_D)
% 1.65/1.87        | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))),
% 1.65/1.87      inference('sup+', [status(thm)], ['189', '221'])).
% 1.65/1.87  thf('223', plain,
% 1.65/1.87      (![X13 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X13)) = (X13))),
% 1.65/1.87      inference('demod', [status(thm)], ['84', '85'])).
% 1.65/1.87  thf('224', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.87      inference('sup-', [status(thm)], ['177', '178'])).
% 1.65/1.87  thf('225', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.65/1.87      inference('sup-', [status(thm)], ['63', '64'])).
% 1.65/1.87  thf('226', plain,
% 1.65/1.87      ((r1_tarski @ (k10_relat_1 @ sk_D @ (k2_relat_1 @ sk_D)) @ sk_B)),
% 1.65/1.87      inference('demod', [status(thm)], ['222', '223', '224', '225'])).
% 1.65/1.87  thf('227', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.65/1.87      inference('sup+', [status(thm)], ['17', '18'])).
% 1.65/1.87  thf(t147_funct_1, axiom,
% 1.65/1.87    (![A:$i,B:$i]:
% 1.65/1.87     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.65/1.87       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 1.65/1.87         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.65/1.87  thf('228', plain,
% 1.65/1.87      (![X18 : $i, X19 : $i]:
% 1.65/1.87         (~ (r1_tarski @ X18 @ (k2_relat_1 @ X19))
% 1.65/1.87          | ((k9_relat_1 @ X19 @ (k10_relat_1 @ X19 @ X18)) = (X18))
% 1.65/1.87          | ~ (v1_funct_1 @ X19)
% 1.65/1.87          | ~ (v1_relat_1 @ X19))),
% 1.65/1.87      inference('cnf', [status(esa)], [t147_funct_1])).
% 1.65/1.87  thf('229', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         (~ (r1_tarski @ X0 @ sk_B)
% 1.65/1.87          | ~ (v1_relat_1 @ sk_C)
% 1.65/1.87          | ~ (v1_funct_1 @ sk_C)
% 1.65/1.87          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 1.65/1.87      inference('sup-', [status(thm)], ['227', '228'])).
% 1.65/1.87  thf('230', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.87      inference('sup-', [status(thm)], ['30', '31'])).
% 1.65/1.87  thf('231', plain, ((v1_funct_1 @ sk_C)),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('232', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         (~ (r1_tarski @ X0 @ sk_B)
% 1.65/1.87          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 1.65/1.87      inference('demod', [status(thm)], ['229', '230', '231'])).
% 1.65/1.87  thf('233', plain,
% 1.65/1.87      (((k9_relat_1 @ sk_C @ 
% 1.65/1.87         (k10_relat_1 @ sk_C @ (k10_relat_1 @ sk_D @ (k2_relat_1 @ sk_D))))
% 1.65/1.87         = (k10_relat_1 @ sk_D @ (k2_relat_1 @ sk_D)))),
% 1.65/1.87      inference('sup-', [status(thm)], ['226', '232'])).
% 1.65/1.87  thf('234', plain,
% 1.65/1.87      ((((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 1.65/1.87          = (k10_relat_1 @ sk_D @ (k2_relat_1 @ sk_D)))
% 1.65/1.87        | ~ (v1_relat_1 @ sk_D))),
% 1.65/1.87      inference('sup+', [status(thm)], ['188', '233'])).
% 1.65/1.87  thf('235', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 1.65/1.87      inference('demod', [status(thm)], ['197', '198'])).
% 1.65/1.87  thf('236', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         (~ (r1_tarski @ X0 @ sk_B)
% 1.65/1.87          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 1.65/1.87      inference('demod', [status(thm)], ['229', '230', '231'])).
% 1.65/1.87  thf('237', plain,
% 1.65/1.87      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 1.65/1.87         = (k1_relat_1 @ sk_D))),
% 1.65/1.87      inference('sup-', [status(thm)], ['235', '236'])).
% 1.65/1.87  thf('238', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.87      inference('sup-', [status(thm)], ['177', '178'])).
% 1.65/1.87  thf('239', plain,
% 1.65/1.87      (((k1_relat_1 @ sk_D) = (k10_relat_1 @ sk_D @ (k2_relat_1 @ sk_D)))),
% 1.65/1.87      inference('demod', [status(thm)], ['234', '237', '238'])).
% 1.65/1.87  thf('240', plain,
% 1.65/1.87      (![X16 : $i]:
% 1.65/1.87         (((k5_relat_1 @ X16 @ (k6_partfun1 @ (k2_relat_1 @ X16))) = (X16))
% 1.65/1.87          | ~ (v1_relat_1 @ X16))),
% 1.65/1.87      inference('demod', [status(thm)], ['190', '191'])).
% 1.65/1.87  thf('241', plain,
% 1.65/1.87      (![X6 : $i, X7 : $i]:
% 1.65/1.87         (~ (v1_relat_1 @ X6)
% 1.65/1.87          | ((k1_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 1.65/1.87              = (k10_relat_1 @ X7 @ (k1_relat_1 @ X6)))
% 1.65/1.87          | ~ (v1_relat_1 @ X7))),
% 1.65/1.87      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.65/1.87  thf('242', plain,
% 1.65/1.87      (![X15 : $i]:
% 1.65/1.87         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X15)) @ X15) = (X15))
% 1.65/1.87          | ~ (v1_relat_1 @ X15))),
% 1.65/1.87      inference('demod', [status(thm)], ['92', '93'])).
% 1.65/1.87  thf('243', plain,
% 1.65/1.87      (![X0 : $i, X1 : $i]:
% 1.65/1.87         (((k5_relat_1 @ 
% 1.65/1.87            (k6_partfun1 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0))) @ 
% 1.65/1.87            (k5_relat_1 @ X1 @ X0)) = (k5_relat_1 @ X1 @ X0))
% 1.65/1.87          | ~ (v1_relat_1 @ X1)
% 1.65/1.87          | ~ (v1_relat_1 @ X0)
% 1.65/1.87          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 1.65/1.87      inference('sup+', [status(thm)], ['241', '242'])).
% 1.65/1.87  thf('244', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         (~ (v1_relat_1 @ X0)
% 1.65/1.87          | ~ (v1_relat_1 @ X0)
% 1.65/1.87          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.65/1.87          | ~ (v1_relat_1 @ X0)
% 1.65/1.87          | ((k5_relat_1 @ 
% 1.65/1.87              (k6_partfun1 @ 
% 1.65/1.87               (k10_relat_1 @ X0 @ 
% 1.65/1.87                (k1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0))))) @ 
% 1.65/1.87              (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 1.65/1.87              = (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))),
% 1.65/1.87      inference('sup-', [status(thm)], ['240', '243'])).
% 1.65/1.87  thf('245', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.65/1.87      inference('sup-', [status(thm)], ['63', '64'])).
% 1.65/1.87  thf('246', plain,
% 1.65/1.87      (![X13 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X13)) = (X13))),
% 1.65/1.87      inference('demod', [status(thm)], ['84', '85'])).
% 1.65/1.87  thf('247', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         (~ (v1_relat_1 @ X0)
% 1.65/1.87          | ~ (v1_relat_1 @ X0)
% 1.65/1.87          | ~ (v1_relat_1 @ X0)
% 1.65/1.87          | ((k5_relat_1 @ 
% 1.65/1.87              (k6_partfun1 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))) @ 
% 1.65/1.87              (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 1.65/1.87              = (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))),
% 1.65/1.87      inference('demod', [status(thm)], ['244', '245', '246'])).
% 1.65/1.87  thf('248', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         (((k5_relat_1 @ 
% 1.65/1.87            (k6_partfun1 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))) @ 
% 1.65/1.87            (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 1.65/1.87            = (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 1.65/1.87          | ~ (v1_relat_1 @ X0))),
% 1.65/1.87      inference('simplify', [status(thm)], ['247'])).
% 1.65/1.87  thf('249', plain,
% 1.65/1.87      ((((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ 
% 1.65/1.87          (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))
% 1.65/1.87          = (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))
% 1.65/1.87        | ~ (v1_relat_1 @ sk_D))),
% 1.65/1.87      inference('sup+', [status(thm)], ['239', '248'])).
% 1.65/1.87  thf('250', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.87      inference('sup-', [status(thm)], ['177', '178'])).
% 1.65/1.87  thf('251', plain,
% 1.65/1.87      (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ 
% 1.65/1.87         (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))
% 1.65/1.87         = (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))),
% 1.65/1.87      inference('demod', [status(thm)], ['249', '250'])).
% 1.65/1.87  thf('252', plain,
% 1.65/1.87      (![X15 : $i]:
% 1.65/1.87         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X15)) @ X15) = (X15))
% 1.65/1.87          | ~ (v1_relat_1 @ X15))),
% 1.65/1.87      inference('demod', [status(thm)], ['92', '93'])).
% 1.65/1.87  thf('253', plain,
% 1.65/1.87      (![X16 : $i]:
% 1.65/1.87         (((k5_relat_1 @ X16 @ (k6_partfun1 @ (k2_relat_1 @ X16))) = (X16))
% 1.65/1.87          | ~ (v1_relat_1 @ X16))),
% 1.65/1.87      inference('demod', [status(thm)], ['190', '191'])).
% 1.65/1.87  thf('254', plain,
% 1.65/1.87      (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ 
% 1.65/1.87         (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))
% 1.65/1.87         = (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))),
% 1.65/1.87      inference('demod', [status(thm)], ['249', '250'])).
% 1.65/1.87  thf('255', plain,
% 1.65/1.87      ((((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D)
% 1.65/1.87          = (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))
% 1.65/1.87        | ~ (v1_relat_1 @ sk_D))),
% 1.65/1.87      inference('sup+', [status(thm)], ['253', '254'])).
% 1.65/1.87  thf('256', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.87      inference('sup-', [status(thm)], ['177', '178'])).
% 1.65/1.87  thf('257', plain,
% 1.65/1.87      (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D)
% 1.65/1.87         = (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))),
% 1.65/1.87      inference('demod', [status(thm)], ['255', '256'])).
% 1.65/1.87  thf('258', plain,
% 1.65/1.87      ((((sk_D) = (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))
% 1.65/1.87        | ~ (v1_relat_1 @ sk_D))),
% 1.65/1.87      inference('sup+', [status(thm)], ['252', '257'])).
% 1.65/1.87  thf('259', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.87      inference('sup-', [status(thm)], ['177', '178'])).
% 1.65/1.87  thf('260', plain,
% 1.65/1.87      (((sk_D) = (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))),
% 1.65/1.87      inference('demod', [status(thm)], ['258', '259'])).
% 1.65/1.87  thf('261', plain,
% 1.65/1.87      (((sk_D) = (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))),
% 1.65/1.87      inference('demod', [status(thm)], ['258', '259'])).
% 1.65/1.87  thf('262', plain,
% 1.65/1.87      (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D) = (sk_D))),
% 1.65/1.87      inference('demod', [status(thm)], ['251', '260', '261'])).
% 1.65/1.87  thf('263', plain,
% 1.65/1.87      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 1.65/1.87         = (k1_relat_1 @ sk_D))),
% 1.65/1.87      inference('sup-', [status(thm)], ['235', '236'])).
% 1.65/1.87  thf('264', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.65/1.87      inference('demod', [status(thm)], ['145', '146', '161'])).
% 1.65/1.87  thf('265', plain,
% 1.65/1.87      (![X6 : $i, X7 : $i]:
% 1.65/1.87         (~ (v1_relat_1 @ X6)
% 1.65/1.87          | ((k1_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 1.65/1.87              = (k10_relat_1 @ X7 @ (k1_relat_1 @ X6)))
% 1.65/1.87          | ~ (v1_relat_1 @ X7))),
% 1.65/1.87      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.65/1.87  thf('266', plain,
% 1.65/1.87      ((((k1_relat_1 @ (k6_partfun1 @ sk_A))
% 1.65/1.87          = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 1.65/1.87        | ~ (v1_relat_1 @ sk_C)
% 1.65/1.87        | ~ (v1_relat_1 @ sk_D))),
% 1.65/1.87      inference('sup+', [status(thm)], ['264', '265'])).
% 1.65/1.87  thf('267', plain,
% 1.65/1.87      (![X13 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X13)) = (X13))),
% 1.65/1.87      inference('demod', [status(thm)], ['84', '85'])).
% 1.65/1.87  thf('268', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.87      inference('sup-', [status(thm)], ['30', '31'])).
% 1.65/1.87  thf('269', plain, ((v1_relat_1 @ sk_D)),
% 1.65/1.87      inference('sup-', [status(thm)], ['177', '178'])).
% 1.65/1.87  thf('270', plain, (((sk_A) = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))),
% 1.65/1.87      inference('demod', [status(thm)], ['266', '267', '268', '269'])).
% 1.65/1.87  thf('271', plain, (((k9_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_D))),
% 1.65/1.87      inference('demod', [status(thm)], ['263', '270'])).
% 1.65/1.87  thf('272', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.65/1.87      inference('simplify', [status(thm)], ['22'])).
% 1.65/1.87  thf('273', plain,
% 1.65/1.87      (![X0 : $i]:
% 1.65/1.87         (~ (r1_tarski @ X0 @ sk_B)
% 1.65/1.87          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 1.65/1.87      inference('demod', [status(thm)], ['229', '230', '231'])).
% 1.65/1.87  thf('274', plain,
% 1.65/1.87      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 1.65/1.87      inference('sup-', [status(thm)], ['272', '273'])).
% 1.65/1.87  thf('275', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.65/1.87      inference('sup+', [status(thm)], ['17', '18'])).
% 1.65/1.87  thf('276', plain,
% 1.65/1.87      (![X5 : $i]:
% 1.65/1.87         (((k10_relat_1 @ X5 @ (k2_relat_1 @ X5)) = (k1_relat_1 @ X5))
% 1.65/1.87          | ~ (v1_relat_1 @ X5))),
% 1.65/1.87      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.65/1.87  thf('277', plain,
% 1.65/1.87      ((((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))
% 1.65/1.87        | ~ (v1_relat_1 @ sk_C))),
% 1.65/1.87      inference('sup+', [status(thm)], ['275', '276'])).
% 1.65/1.87  thf('278', plain, ((v1_relat_1 @ sk_C)),
% 1.65/1.87      inference('sup-', [status(thm)], ['30', '31'])).
% 1.65/1.87  thf('279', plain, (((k10_relat_1 @ sk_C @ sk_B) = (k1_relat_1 @ sk_C))),
% 1.65/1.87      inference('demod', [status(thm)], ['277', '278'])).
% 1.65/1.87  thf('280', plain, (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (sk_B))),
% 1.65/1.87      inference('demod', [status(thm)], ['274', '279'])).
% 1.65/1.87  thf('281', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 1.65/1.87      inference('demod', [status(thm)],
% 1.65/1.87                ['166', '167', '174', '175', '176', '179', '180'])).
% 1.65/1.87  thf('282', plain, (((k9_relat_1 @ sk_C @ sk_A) = (sk_B))),
% 1.65/1.87      inference('demod', [status(thm)], ['280', '281'])).
% 1.65/1.87  thf('283', plain, (((k1_relat_1 @ sk_D) = (sk_B))),
% 1.65/1.87      inference('sup+', [status(thm)], ['271', '282'])).
% 1.65/1.87  thf('284', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 1.65/1.87      inference('demod', [status(thm)], ['262', '283'])).
% 1.65/1.87  thf('285', plain,
% 1.65/1.87      (((sk_D) = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))),
% 1.65/1.87      inference('demod', [status(thm)], ['187', '284'])).
% 1.65/1.87  thf('286', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 1.65/1.87      inference('sup+', [status(thm)], ['182', '285'])).
% 1.65/1.87  thf('287', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.65/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.65/1.87  thf('288', plain, ($false),
% 1.65/1.87      inference('simplify_reflect-', [status(thm)], ['286', '287'])).
% 1.65/1.87  
% 1.65/1.87  % SZS output end Refutation
% 1.65/1.87  
% 1.65/1.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
