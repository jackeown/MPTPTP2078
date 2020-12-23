%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KnlHgpSQVV

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:14 EST 2020

% Result     : Theorem 1.68s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :  386 (3354 expanded)
%              Number of leaves         :   49 (1079 expanded)
%              Depth                    :   42
%              Number of atoms          : 3195 (53954 expanded)
%              Number of equality atoms :  198 (3656 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
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
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k5_relat_1 @ X25 @ ( k2_funct_1 @ X25 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k5_relat_1 @ X25 @ ( k2_funct_1 @ X25 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('5',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X25 ) @ X25 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('6',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('7',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X25 ) @ X25 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X25 ) @ X25 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('9',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X25 ) @ X25 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('10',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X25 ) @ X25 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('11',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X25 ) @ X25 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('12',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
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
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relat_1 @ X24 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('14',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
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
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('21',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k2_relat_1 @ X24 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('33',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['29','34','35','36'])).

thf('38',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['13','45'])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['17','18'])).

thf('48',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('49',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('50',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['46','47','48','49','50','51'])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('53',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ( v4_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v4_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','60'])).

thf('62',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('63',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('64',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('65',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('74',plain,(
    v4_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['61','62','69','70','71','72','73'])).

thf('75',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('76',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','76'])).

thf('78',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['17','18'])).

thf('79',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('80',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('81',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['77','78','79','80','81','82'])).

thf('84',plain,
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

thf('85',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X22 @ ( k2_relat_1 @ X23 ) )
      | ( ( k9_relat_1 @ X23 @ ( k10_relat_1 @ X23 @ X22 ) )
        = X22 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ) )
    = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['83','89'])).

thf('91',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ) ) )
      = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['9','90'])).

thf('92',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('93',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('94',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('95',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('97',plain,(
    ! [X20: $i] :
      ( ( ( k5_relat_1 @ X20 @ ( k6_relat_1 @ ( k2_relat_1 @ X20 ) ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('98',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('99',plain,(
    ! [X20: $i] :
      ( ( ( k5_relat_1 @ X20 @ ( k6_partfun1 @ ( k2_relat_1 @ X20 ) ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['96','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('102',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['100','101'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('103',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) )
        = ( k10_relat_1 @ X11 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('104',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('106',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('107',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('108',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf('109',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['100','101'])).

thf('110',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) )
        = ( k10_relat_1 @ X11 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('111',plain,(
    ! [X9: $i] :
      ( ( ( k9_relat_1 @ X9 @ ( k1_relat_1 @ X9 ) )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k9_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ) )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('115',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('116',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('117',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['100','101'])).

thf('118',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('119',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['100','101'])).

thf('120',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['17','18'])).

thf('121',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['113','114','115','116','117','118','119','120'])).

thf('122',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf('123',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('125',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['91','92','95','108','123','124','125','126'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('128',plain,(
    ! [X19: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X19 ) ) @ X19 )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('129',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('130',plain,(
    ! [X19: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X19 ) ) @ X19 )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['127','130'])).

thf('132',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','131'])).

thf('133',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['17','18'])).

thf('134',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('135',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('136',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['132','133','134','135','136','137'])).

thf('139',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['7','138'])).

thf('140',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['17','18'])).

thf('141',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('142',plain,(
    ! [X19: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X19 ) ) @ X19 )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('147',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( k6_partfun1 @ sk_B )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['139','140','145','146','147','148'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('150',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) @ X16 )
        = ( k5_relat_1 @ X15 @ ( k5_relat_1 @ X14 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','153'])).

thf('155',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('156',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('158',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['3','157'])).

thf('159',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('160',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['46','47','48','49','50','51'])).

thf('161',plain,(
    ! [X19: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X19 ) ) @ X19 )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('162',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['159','162'])).

thf('164',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('165',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['163','164','165'])).

thf('167',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('168',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['158','166','167','168','169'])).

thf('171',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['0','170'])).

thf('172',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('173',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['171','172','173'])).

thf('175',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
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

thf('177',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46 )
        = ( k5_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('178',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['175','180'])).

thf('182',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
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

thf('186',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('187',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['184','189'])).

thf('191',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('193',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( X32 = X35 )
      | ~ ( r2_relset_1 @ X33 @ X34 @ X32 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('194',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['183','194'])).

thf('196',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('197',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['181','182','197'])).

thf('199',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('200',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['198','201'])).

thf('203',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('204',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('205',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('206',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('208',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('210',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['208','209'])).

thf('211',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['181','182','197'])).

thf('212',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('213',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('215',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('217',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['215','216'])).

thf('218',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('219',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['202','203','210','211','212','217','218'])).

thf('220',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['174','219'])).

thf('221',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['181','182','197'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('223',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['221','222'])).

thf('224',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['215','216'])).

thf('225',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X20: $i] :
      ( ( ( k5_relat_1 @ X20 @ ( k6_partfun1 @ ( k2_relat_1 @ X20 ) ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('227',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) )
        = ( k10_relat_1 @ X11 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('228',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['226','227'])).

thf('229',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('230',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['228','229','230'])).

thf('232',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['231'])).

thf('233',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) )
        = ( k10_relat_1 @ X11 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('234',plain,(
    ! [X20: $i] :
      ( ( ( k5_relat_1 @ X20 @ ( k6_partfun1 @ ( k2_relat_1 @ X20 ) ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('235',plain,(
    ! [X19: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X19 ) ) @ X19 )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('236',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) @ X16 )
        = ( k5_relat_1 @ X15 @ ( k5_relat_1 @ X14 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('237',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['235','236'])).

thf('238',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('239',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['237','238'])).

thf('240',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['239'])).

thf('241',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['234','240'])).

thf('242',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('243',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['241','242'])).

thf('244',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['243'])).

thf('245',plain,(
    ! [X19: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X19 ) ) @ X19 )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('246',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('248',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['246','247'])).

thf('249',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('250',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['248','249'])).

thf('251',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['215','216'])).

thf('252',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['250','251'])).

thf('253',plain,(
    ! [X19: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X19 ) ) @ X19 )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('254',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('255',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) )
        = ( k10_relat_1 @ X11 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('256',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k6_partfun1 @ X0 ) )
        = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['254','255'])).

thf('257',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('258',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('259',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('260',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('261',plain,(
    ! [X0: $i] :
      ( X0
      = ( k10_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['256','257','258','259','260'])).

thf('262',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) )
        = ( k10_relat_1 @ X11 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('263',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('264',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['262','263'])).

thf('265',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( v4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['261','264'])).

thf('266',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('267',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( v4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['265','266'])).

thf('268',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['253','267'])).

thf('269',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( v4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['268'])).

thf('270',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( v4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['252','269'])).

thf('271',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['215','216'])).

thf('272',plain,(
    v4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['270','271'])).

thf('273',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('274',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['272','273'])).

thf('275',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['245','274'])).

thf('276',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['215','216'])).

thf('277',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['215','216'])).

thf('278',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) ) @ sk_B ),
    inference(demod,[status(thm)],['275','276','277'])).

thf('279',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['244','278'])).

thf('280',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['215','216'])).

thf('281',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ) @ sk_B ),
    inference(demod,[status(thm)],['279','280'])).

thf('282',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_D @ ( k1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['233','281'])).

thf('283',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('284',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['215','216'])).

thf('285',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('286',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_D @ ( k2_relat_1 @ sk_D ) ) @ sk_B ),
    inference(demod,[status(thm)],['282','283','284','285'])).

thf('287',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('288',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k10_relat_1 @ sk_D @ ( k2_relat_1 @ sk_D ) ) ) )
    = ( k10_relat_1 @ sk_D @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['286','287'])).

thf('289',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
      = ( k10_relat_1 @ sk_D @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['232','288'])).

thf('290',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['250','251'])).

thf('291',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('292',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['290','291'])).

thf('293',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['215','216'])).

thf('294',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k10_relat_1 @ sk_D @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['289','292','293'])).

thf('295',plain,(
    ! [X20: $i] :
      ( ( ( k5_relat_1 @ X20 @ ( k6_partfun1 @ ( k2_relat_1 @ X20 ) ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('296',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) )
        = ( k10_relat_1 @ X11 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('297',plain,(
    ! [X19: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X19 ) ) @ X19 )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('298',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) ) @ ( k5_relat_1 @ X1 @ X0 ) )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['296','297'])).

thf('299',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['295','298'])).

thf('300',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('301',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('302',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['299','300','301'])).

thf('303',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
        = ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['302'])).

thf('304',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) )
      = ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['294','303'])).

thf('305',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['215','216'])).

thf('306',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) )
    = ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['304','305'])).

thf('307',plain,(
    ! [X19: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X19 ) ) @ X19 )
        = X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('308',plain,(
    ! [X20: $i] :
      ( ( ( k5_relat_1 @ X20 @ ( k6_partfun1 @ ( k2_relat_1 @ X20 ) ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('309',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) )
    = ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['304','305'])).

thf('310',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D )
      = ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['308','309'])).

thf('311',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['215','216'])).

thf('312',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D )
    = ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['310','311'])).

thf('313',plain,
    ( ( sk_D
      = ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['307','312'])).

thf('314',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['215','216'])).

thf('315',plain,
    ( sk_D
    = ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['313','314'])).

thf('316',plain,
    ( sk_D
    = ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['313','314'])).

thf('317',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['306','315','316'])).

thf('318',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['290','291'])).

thf('319',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['181','182','197'])).

thf('320',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) )
        = ( k10_relat_1 @ X11 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('321',plain,
    ( ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
      = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['319','320'])).

thf('322',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('323',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('324',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['215','216'])).

thf('325',plain,
    ( sk_A
    = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['321','322','323','324'])).

thf('326',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['318','325'])).

thf('327',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['121','122'])).

thf('328',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['202','203','210','211','212','217','218'])).

thf('329',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['327','328'])).

thf('330',plain,
    ( ( k1_relat_1 @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['326','329'])).

thf('331',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['317','330'])).

thf('332',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['225','331'])).

thf('333',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['220','332'])).

thf('334',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('335',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['333','334'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KnlHgpSQVV
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:37:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.68/1.87  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.68/1.87  % Solved by: fo/fo7.sh
% 1.68/1.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.68/1.87  % done 1890 iterations in 1.409s
% 1.68/1.87  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.68/1.87  % SZS output start Refutation
% 1.68/1.87  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.68/1.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.68/1.87  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.68/1.87  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.68/1.87  thf(sk_D_type, type, sk_D: $i).
% 1.68/1.87  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.68/1.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.68/1.87  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.68/1.87  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.68/1.87  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.68/1.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.68/1.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.68/1.87  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.68/1.87  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.68/1.87  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.68/1.87  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.68/1.87  thf(sk_B_type, type, sk_B: $i).
% 1.68/1.87  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.68/1.87  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.68/1.87  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.68/1.87  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.68/1.87  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.68/1.87  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.68/1.87  thf(sk_A_type, type, sk_A: $i).
% 1.68/1.87  thf(sk_C_type, type, sk_C: $i).
% 1.68/1.87  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.68/1.87  thf(dt_k2_funct_1, axiom,
% 1.68/1.87    (![A:$i]:
% 1.68/1.87     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.68/1.87       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.68/1.87         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.68/1.87  thf('0', plain,
% 1.68/1.87      (![X21 : $i]:
% 1.68/1.87         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 1.68/1.87          | ~ (v1_funct_1 @ X21)
% 1.68/1.87          | ~ (v1_relat_1 @ X21))),
% 1.68/1.87      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.68/1.87  thf(t61_funct_1, axiom,
% 1.68/1.87    (![A:$i]:
% 1.68/1.87     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.68/1.87       ( ( v2_funct_1 @ A ) =>
% 1.68/1.87         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.68/1.87             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.68/1.87           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.68/1.87             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.68/1.87  thf('1', plain,
% 1.68/1.87      (![X25 : $i]:
% 1.68/1.87         (~ (v2_funct_1 @ X25)
% 1.68/1.87          | ((k5_relat_1 @ X25 @ (k2_funct_1 @ X25))
% 1.68/1.87              = (k6_relat_1 @ (k1_relat_1 @ X25)))
% 1.68/1.87          | ~ (v1_funct_1 @ X25)
% 1.68/1.87          | ~ (v1_relat_1 @ X25))),
% 1.68/1.87      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.68/1.87  thf(redefinition_k6_partfun1, axiom,
% 1.68/1.87    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.68/1.87  thf('2', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 1.68/1.87      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.68/1.87  thf('3', plain,
% 1.68/1.87      (![X25 : $i]:
% 1.68/1.87         (~ (v2_funct_1 @ X25)
% 1.68/1.87          | ((k5_relat_1 @ X25 @ (k2_funct_1 @ X25))
% 1.68/1.87              = (k6_partfun1 @ (k1_relat_1 @ X25)))
% 1.68/1.87          | ~ (v1_funct_1 @ X25)
% 1.68/1.87          | ~ (v1_relat_1 @ X25))),
% 1.68/1.87      inference('demod', [status(thm)], ['1', '2'])).
% 1.68/1.87  thf('4', plain,
% 1.68/1.87      (![X21 : $i]:
% 1.68/1.87         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 1.68/1.87          | ~ (v1_funct_1 @ X21)
% 1.68/1.87          | ~ (v1_relat_1 @ X21))),
% 1.68/1.87      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.68/1.87  thf('5', plain,
% 1.68/1.87      (![X25 : $i]:
% 1.68/1.87         (~ (v2_funct_1 @ X25)
% 1.68/1.87          | ((k5_relat_1 @ (k2_funct_1 @ X25) @ X25)
% 1.68/1.87              = (k6_relat_1 @ (k2_relat_1 @ X25)))
% 1.68/1.87          | ~ (v1_funct_1 @ X25)
% 1.68/1.87          | ~ (v1_relat_1 @ X25))),
% 1.68/1.87      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.68/1.87  thf('6', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 1.68/1.87      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.68/1.87  thf('7', plain,
% 1.68/1.87      (![X25 : $i]:
% 1.68/1.87         (~ (v2_funct_1 @ X25)
% 1.68/1.87          | ((k5_relat_1 @ (k2_funct_1 @ X25) @ X25)
% 1.68/1.87              = (k6_partfun1 @ (k2_relat_1 @ X25)))
% 1.68/1.87          | ~ (v1_funct_1 @ X25)
% 1.68/1.87          | ~ (v1_relat_1 @ X25))),
% 1.68/1.87      inference('demod', [status(thm)], ['5', '6'])).
% 1.68/1.87  thf('8', plain,
% 1.68/1.87      (![X25 : $i]:
% 1.68/1.87         (~ (v2_funct_1 @ X25)
% 1.68/1.87          | ((k5_relat_1 @ (k2_funct_1 @ X25) @ X25)
% 1.68/1.87              = (k6_partfun1 @ (k2_relat_1 @ X25)))
% 1.68/1.87          | ~ (v1_funct_1 @ X25)
% 1.68/1.87          | ~ (v1_relat_1 @ X25))),
% 1.68/1.87      inference('demod', [status(thm)], ['5', '6'])).
% 1.68/1.87  thf('9', plain,
% 1.68/1.87      (![X25 : $i]:
% 1.68/1.87         (~ (v2_funct_1 @ X25)
% 1.68/1.87          | ((k5_relat_1 @ (k2_funct_1 @ X25) @ X25)
% 1.68/1.87              = (k6_partfun1 @ (k2_relat_1 @ X25)))
% 1.68/1.87          | ~ (v1_funct_1 @ X25)
% 1.68/1.87          | ~ (v1_relat_1 @ X25))),
% 1.68/1.87      inference('demod', [status(thm)], ['5', '6'])).
% 1.68/1.87  thf('10', plain,
% 1.68/1.87      (![X25 : $i]:
% 1.68/1.87         (~ (v2_funct_1 @ X25)
% 1.68/1.87          | ((k5_relat_1 @ (k2_funct_1 @ X25) @ X25)
% 1.68/1.87              = (k6_partfun1 @ (k2_relat_1 @ X25)))
% 1.68/1.87          | ~ (v1_funct_1 @ X25)
% 1.68/1.87          | ~ (v1_relat_1 @ X25))),
% 1.68/1.87      inference('demod', [status(thm)], ['5', '6'])).
% 1.68/1.87  thf('11', plain,
% 1.68/1.87      (![X25 : $i]:
% 1.68/1.87         (~ (v2_funct_1 @ X25)
% 1.68/1.87          | ((k5_relat_1 @ (k2_funct_1 @ X25) @ X25)
% 1.68/1.87              = (k6_partfun1 @ (k2_relat_1 @ X25)))
% 1.68/1.87          | ~ (v1_funct_1 @ X25)
% 1.68/1.87          | ~ (v1_relat_1 @ X25))),
% 1.68/1.87      inference('demod', [status(thm)], ['5', '6'])).
% 1.68/1.87  thf('12', plain,
% 1.68/1.87      (![X21 : $i]:
% 1.68/1.87         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 1.68/1.87          | ~ (v1_funct_1 @ X21)
% 1.68/1.87          | ~ (v1_relat_1 @ X21))),
% 1.68/1.87      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.68/1.87  thf(t55_funct_1, axiom,
% 1.68/1.87    (![A:$i]:
% 1.68/1.87     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.68/1.87       ( ( v2_funct_1 @ A ) =>
% 1.68/1.87         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.68/1.87           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.68/1.87  thf('13', plain,
% 1.68/1.87      (![X24 : $i]:
% 1.68/1.87         (~ (v2_funct_1 @ X24)
% 1.68/1.87          | ((k2_relat_1 @ X24) = (k1_relat_1 @ (k2_funct_1 @ X24)))
% 1.68/1.87          | ~ (v1_funct_1 @ X24)
% 1.68/1.87          | ~ (v1_relat_1 @ X24))),
% 1.68/1.87      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.68/1.87  thf('14', plain,
% 1.68/1.87      (![X21 : $i]:
% 1.68/1.87         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 1.68/1.87          | ~ (v1_funct_1 @ X21)
% 1.68/1.87          | ~ (v1_relat_1 @ X21))),
% 1.68/1.87      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.68/1.87  thf(t36_funct_2, conjecture,
% 1.68/1.87    (![A:$i,B:$i,C:$i]:
% 1.68/1.87     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.68/1.87         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.68/1.87       ( ![D:$i]:
% 1.68/1.87         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.68/1.87             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.68/1.87           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.68/1.87               ( r2_relset_1 @
% 1.68/1.87                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.68/1.87                 ( k6_partfun1 @ A ) ) & 
% 1.68/1.87               ( v2_funct_1 @ C ) ) =>
% 1.68/1.87             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.68/1.87               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.68/1.87  thf(zf_stmt_0, negated_conjecture,
% 1.68/1.87    (~( ![A:$i,B:$i,C:$i]:
% 1.68/1.87        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.68/1.87            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.68/1.87          ( ![D:$i]:
% 1.68/1.87            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.68/1.87                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.68/1.87              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.68/1.87                  ( r2_relset_1 @
% 1.68/1.87                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.68/1.87                    ( k6_partfun1 @ A ) ) & 
% 1.68/1.87                  ( v2_funct_1 @ C ) ) =>
% 1.68/1.87                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.68/1.87                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.68/1.87    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.68/1.87  thf('15', plain,
% 1.68/1.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf(redefinition_k2_relset_1, axiom,
% 1.68/1.87    (![A:$i,B:$i,C:$i]:
% 1.68/1.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.68/1.87       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.68/1.87  thf('16', plain,
% 1.68/1.87      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.68/1.87         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 1.68/1.87          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.68/1.87      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.68/1.87  thf('17', plain,
% 1.68/1.87      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.68/1.87      inference('sup-', [status(thm)], ['15', '16'])).
% 1.68/1.87  thf('18', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('19', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.68/1.87      inference('sup+', [status(thm)], ['17', '18'])).
% 1.68/1.87  thf('20', plain,
% 1.68/1.87      (![X21 : $i]:
% 1.68/1.87         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 1.68/1.87          | ~ (v1_funct_1 @ X21)
% 1.68/1.87          | ~ (v1_relat_1 @ X21))),
% 1.68/1.87      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.68/1.87  thf('21', plain,
% 1.68/1.87      (![X24 : $i]:
% 1.68/1.87         (~ (v2_funct_1 @ X24)
% 1.68/1.87          | ((k2_relat_1 @ X24) = (k1_relat_1 @ (k2_funct_1 @ X24)))
% 1.68/1.87          | ~ (v1_funct_1 @ X24)
% 1.68/1.87          | ~ (v1_relat_1 @ X24))),
% 1.68/1.87      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.68/1.87  thf(d10_xboole_0, axiom,
% 1.68/1.87    (![A:$i,B:$i]:
% 1.68/1.87     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.68/1.87  thf('22', plain,
% 1.68/1.87      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.68/1.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.68/1.87  thf('23', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.68/1.87      inference('simplify', [status(thm)], ['22'])).
% 1.68/1.87  thf(d18_relat_1, axiom,
% 1.68/1.87    (![A:$i,B:$i]:
% 1.68/1.87     ( ( v1_relat_1 @ B ) =>
% 1.68/1.87       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.68/1.87  thf('24', plain,
% 1.68/1.87      (![X5 : $i, X6 : $i]:
% 1.68/1.87         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.68/1.87          | (v4_relat_1 @ X5 @ X6)
% 1.68/1.87          | ~ (v1_relat_1 @ X5))),
% 1.68/1.87      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.68/1.87  thf('25', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 1.68/1.87      inference('sup-', [status(thm)], ['23', '24'])).
% 1.68/1.87  thf('26', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.68/1.87          | ~ (v1_relat_1 @ X0)
% 1.68/1.87          | ~ (v1_funct_1 @ X0)
% 1.68/1.87          | ~ (v2_funct_1 @ X0)
% 1.68/1.87          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.68/1.87      inference('sup+', [status(thm)], ['21', '25'])).
% 1.68/1.87  thf('27', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ X0)
% 1.68/1.87          | ~ (v1_funct_1 @ X0)
% 1.68/1.87          | ~ (v2_funct_1 @ X0)
% 1.68/1.87          | ~ (v1_funct_1 @ X0)
% 1.68/1.87          | ~ (v1_relat_1 @ X0)
% 1.68/1.87          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.68/1.87      inference('sup-', [status(thm)], ['20', '26'])).
% 1.68/1.87  thf('28', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.68/1.87          | ~ (v2_funct_1 @ X0)
% 1.68/1.87          | ~ (v1_funct_1 @ X0)
% 1.68/1.87          | ~ (v1_relat_1 @ X0))),
% 1.68/1.87      inference('simplify', [status(thm)], ['27'])).
% 1.68/1.87  thf('29', plain,
% 1.68/1.87      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 1.68/1.87        | ~ (v1_relat_1 @ sk_C)
% 1.68/1.87        | ~ (v1_funct_1 @ sk_C)
% 1.68/1.87        | ~ (v2_funct_1 @ sk_C))),
% 1.68/1.87      inference('sup+', [status(thm)], ['19', '28'])).
% 1.68/1.87  thf('30', plain,
% 1.68/1.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf(cc2_relat_1, axiom,
% 1.68/1.87    (![A:$i]:
% 1.68/1.87     ( ( v1_relat_1 @ A ) =>
% 1.68/1.87       ( ![B:$i]:
% 1.68/1.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.68/1.87  thf('31', plain,
% 1.68/1.87      (![X3 : $i, X4 : $i]:
% 1.68/1.87         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.68/1.87          | (v1_relat_1 @ X3)
% 1.68/1.87          | ~ (v1_relat_1 @ X4))),
% 1.68/1.87      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.68/1.87  thf('32', plain,
% 1.68/1.87      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.68/1.87      inference('sup-', [status(thm)], ['30', '31'])).
% 1.68/1.87  thf(fc6_relat_1, axiom,
% 1.68/1.87    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.68/1.87  thf('33', plain,
% 1.68/1.87      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 1.68/1.87      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.68/1.87  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 1.68/1.87      inference('demod', [status(thm)], ['32', '33'])).
% 1.68/1.87  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('36', plain, ((v2_funct_1 @ sk_C)),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('37', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 1.68/1.87      inference('demod', [status(thm)], ['29', '34', '35', '36'])).
% 1.68/1.87  thf('38', plain,
% 1.68/1.87      (![X5 : $i, X6 : $i]:
% 1.68/1.87         (~ (v4_relat_1 @ X5 @ X6)
% 1.68/1.87          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.68/1.87          | ~ (v1_relat_1 @ X5))),
% 1.68/1.87      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.68/1.87  thf('39', plain,
% 1.68/1.87      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.68/1.87        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.68/1.87      inference('sup-', [status(thm)], ['37', '38'])).
% 1.68/1.87  thf('40', plain,
% 1.68/1.87      ((~ (v1_relat_1 @ sk_C)
% 1.68/1.87        | ~ (v1_funct_1 @ sk_C)
% 1.68/1.87        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.68/1.87      inference('sup-', [status(thm)], ['14', '39'])).
% 1.68/1.87  thf('41', plain, ((v1_relat_1 @ sk_C)),
% 1.68/1.87      inference('demod', [status(thm)], ['32', '33'])).
% 1.68/1.87  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('43', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 1.68/1.87      inference('demod', [status(thm)], ['40', '41', '42'])).
% 1.68/1.87  thf('44', plain,
% 1.68/1.87      (![X0 : $i, X2 : $i]:
% 1.68/1.87         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.68/1.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.68/1.87  thf('45', plain,
% 1.68/1.87      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.68/1.87        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.68/1.87      inference('sup-', [status(thm)], ['43', '44'])).
% 1.68/1.87  thf('46', plain,
% 1.68/1.87      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 1.68/1.87        | ~ (v1_relat_1 @ sk_C)
% 1.68/1.87        | ~ (v1_funct_1 @ sk_C)
% 1.68/1.87        | ~ (v2_funct_1 @ sk_C)
% 1.68/1.87        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.68/1.87      inference('sup-', [status(thm)], ['13', '45'])).
% 1.68/1.87  thf('47', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.68/1.87      inference('sup+', [status(thm)], ['17', '18'])).
% 1.68/1.87  thf('48', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.68/1.87      inference('simplify', [status(thm)], ['22'])).
% 1.68/1.87  thf('49', plain, ((v1_relat_1 @ sk_C)),
% 1.68/1.87      inference('demod', [status(thm)], ['32', '33'])).
% 1.68/1.87  thf('50', plain, ((v1_funct_1 @ sk_C)),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('51', plain, ((v2_funct_1 @ sk_C)),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('52', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.68/1.87      inference('demod', [status(thm)], ['46', '47', '48', '49', '50', '51'])).
% 1.68/1.87  thf(t44_relat_1, axiom,
% 1.68/1.87    (![A:$i]:
% 1.68/1.87     ( ( v1_relat_1 @ A ) =>
% 1.68/1.87       ( ![B:$i]:
% 1.68/1.87         ( ( v1_relat_1 @ B ) =>
% 1.68/1.87           ( r1_tarski @
% 1.68/1.87             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 1.68/1.87  thf('53', plain,
% 1.68/1.87      (![X12 : $i, X13 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ X12)
% 1.68/1.87          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X13 @ X12)) @ 
% 1.68/1.87             (k1_relat_1 @ X13))
% 1.68/1.87          | ~ (v1_relat_1 @ X13))),
% 1.68/1.87      inference('cnf', [status(esa)], [t44_relat_1])).
% 1.68/1.87  thf('54', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         ((r1_tarski @ 
% 1.68/1.87           (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)) @ sk_B)
% 1.68/1.87          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.68/1.87          | ~ (v1_relat_1 @ X0))),
% 1.68/1.87      inference('sup+', [status(thm)], ['52', '53'])).
% 1.68/1.87  thf('55', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ sk_C)
% 1.68/1.87          | ~ (v1_funct_1 @ sk_C)
% 1.68/1.87          | ~ (v1_relat_1 @ X0)
% 1.68/1.87          | (r1_tarski @ 
% 1.68/1.87             (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)) @ sk_B))),
% 1.68/1.87      inference('sup-', [status(thm)], ['12', '54'])).
% 1.68/1.87  thf('56', plain, ((v1_relat_1 @ sk_C)),
% 1.68/1.87      inference('demod', [status(thm)], ['32', '33'])).
% 1.68/1.87  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('58', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ X0)
% 1.68/1.87          | (r1_tarski @ 
% 1.68/1.87             (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)) @ sk_B))),
% 1.68/1.87      inference('demod', [status(thm)], ['55', '56', '57'])).
% 1.68/1.87  thf('59', plain,
% 1.68/1.87      (![X5 : $i, X6 : $i]:
% 1.68/1.87         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.68/1.87          | (v4_relat_1 @ X5 @ X6)
% 1.68/1.87          | ~ (v1_relat_1 @ X5))),
% 1.68/1.87      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.68/1.87  thf('60', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ X0)
% 1.68/1.87          | ~ (v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))
% 1.68/1.87          | (v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0) @ sk_B))),
% 1.68/1.87      inference('sup-', [status(thm)], ['58', '59'])).
% 1.68/1.87  thf('61', plain,
% 1.68/1.87      ((~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.68/1.87        | ~ (v1_relat_1 @ sk_C)
% 1.68/1.87        | ~ (v1_funct_1 @ sk_C)
% 1.68/1.87        | ~ (v2_funct_1 @ sk_C)
% 1.68/1.87        | (v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) @ sk_B)
% 1.68/1.87        | ~ (v1_relat_1 @ sk_C))),
% 1.68/1.87      inference('sup-', [status(thm)], ['11', '60'])).
% 1.68/1.87  thf('62', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.68/1.87      inference('sup+', [status(thm)], ['17', '18'])).
% 1.68/1.87  thf(t29_relset_1, axiom,
% 1.68/1.87    (![A:$i]:
% 1.68/1.87     ( m1_subset_1 @
% 1.68/1.87       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.68/1.87  thf('63', plain,
% 1.68/1.87      (![X36 : $i]:
% 1.68/1.87         (m1_subset_1 @ (k6_relat_1 @ X36) @ 
% 1.68/1.87          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 1.68/1.87      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.68/1.87  thf('64', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 1.68/1.87      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.68/1.87  thf('65', plain,
% 1.68/1.87      (![X36 : $i]:
% 1.68/1.87         (m1_subset_1 @ (k6_partfun1 @ X36) @ 
% 1.68/1.87          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 1.68/1.87      inference('demod', [status(thm)], ['63', '64'])).
% 1.68/1.87  thf('66', plain,
% 1.68/1.87      (![X3 : $i, X4 : $i]:
% 1.68/1.87         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.68/1.87          | (v1_relat_1 @ X3)
% 1.68/1.87          | ~ (v1_relat_1 @ X4))),
% 1.68/1.87      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.68/1.87  thf('67', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X0))
% 1.68/1.87          | (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.68/1.87      inference('sup-', [status(thm)], ['65', '66'])).
% 1.68/1.87  thf('68', plain,
% 1.68/1.87      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 1.68/1.87      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.68/1.87  thf('69', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.68/1.87      inference('demod', [status(thm)], ['67', '68'])).
% 1.68/1.87  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 1.68/1.87      inference('demod', [status(thm)], ['32', '33'])).
% 1.68/1.87  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('72', plain, ((v2_funct_1 @ sk_C)),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('73', plain, ((v1_relat_1 @ sk_C)),
% 1.68/1.87      inference('demod', [status(thm)], ['32', '33'])).
% 1.68/1.87  thf('74', plain,
% 1.68/1.87      ((v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) @ sk_B)),
% 1.68/1.87      inference('demod', [status(thm)],
% 1.68/1.87                ['61', '62', '69', '70', '71', '72', '73'])).
% 1.68/1.87  thf('75', plain,
% 1.68/1.87      (![X5 : $i, X6 : $i]:
% 1.68/1.87         (~ (v4_relat_1 @ X5 @ X6)
% 1.68/1.87          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.68/1.87          | ~ (v1_relat_1 @ X5))),
% 1.68/1.87      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.68/1.87  thf('76', plain,
% 1.68/1.87      ((~ (v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.68/1.87        | (r1_tarski @ 
% 1.68/1.87           (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)) @ sk_B))),
% 1.68/1.87      inference('sup-', [status(thm)], ['74', '75'])).
% 1.68/1.87  thf('77', plain,
% 1.68/1.87      ((~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.68/1.87        | ~ (v1_relat_1 @ sk_C)
% 1.68/1.87        | ~ (v1_funct_1 @ sk_C)
% 1.68/1.87        | ~ (v2_funct_1 @ sk_C)
% 1.68/1.87        | (r1_tarski @ 
% 1.68/1.87           (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)) @ sk_B))),
% 1.68/1.87      inference('sup-', [status(thm)], ['10', '76'])).
% 1.68/1.87  thf('78', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.68/1.87      inference('sup+', [status(thm)], ['17', '18'])).
% 1.68/1.87  thf('79', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.68/1.87      inference('demod', [status(thm)], ['67', '68'])).
% 1.68/1.87  thf('80', plain, ((v1_relat_1 @ sk_C)),
% 1.68/1.87      inference('demod', [status(thm)], ['32', '33'])).
% 1.68/1.87  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('82', plain, ((v2_funct_1 @ sk_C)),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('83', plain,
% 1.68/1.87      ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)) @ 
% 1.68/1.87        sk_B)),
% 1.68/1.87      inference('demod', [status(thm)], ['77', '78', '79', '80', '81', '82'])).
% 1.68/1.87  thf('84', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.68/1.87      inference('sup+', [status(thm)], ['17', '18'])).
% 1.68/1.87  thf(t147_funct_1, axiom,
% 1.68/1.87    (![A:$i,B:$i]:
% 1.68/1.87     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.68/1.87       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 1.68/1.87         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 1.68/1.87  thf('85', plain,
% 1.68/1.87      (![X22 : $i, X23 : $i]:
% 1.68/1.87         (~ (r1_tarski @ X22 @ (k2_relat_1 @ X23))
% 1.68/1.87          | ((k9_relat_1 @ X23 @ (k10_relat_1 @ X23 @ X22)) = (X22))
% 1.68/1.87          | ~ (v1_funct_1 @ X23)
% 1.68/1.87          | ~ (v1_relat_1 @ X23))),
% 1.68/1.87      inference('cnf', [status(esa)], [t147_funct_1])).
% 1.68/1.87  thf('86', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         (~ (r1_tarski @ X0 @ sk_B)
% 1.68/1.87          | ~ (v1_relat_1 @ sk_C)
% 1.68/1.87          | ~ (v1_funct_1 @ sk_C)
% 1.68/1.87          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 1.68/1.87      inference('sup-', [status(thm)], ['84', '85'])).
% 1.68/1.87  thf('87', plain, ((v1_relat_1 @ sk_C)),
% 1.68/1.87      inference('demod', [status(thm)], ['32', '33'])).
% 1.68/1.87  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('89', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         (~ (r1_tarski @ X0 @ sk_B)
% 1.68/1.87          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 1.68/1.87      inference('demod', [status(thm)], ['86', '87', '88'])).
% 1.68/1.87  thf('90', plain,
% 1.68/1.87      (((k9_relat_1 @ sk_C @ 
% 1.68/1.87         (k10_relat_1 @ sk_C @ 
% 1.68/1.87          (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))))
% 1.68/1.87         = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 1.68/1.87      inference('sup-', [status(thm)], ['83', '89'])).
% 1.68/1.87  thf('91', plain,
% 1.68/1.87      ((((k9_relat_1 @ sk_C @ 
% 1.68/1.87          (k10_relat_1 @ sk_C @ 
% 1.68/1.87           (k1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)))))
% 1.68/1.87          = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))
% 1.68/1.87        | ~ (v1_relat_1 @ sk_C)
% 1.68/1.87        | ~ (v1_funct_1 @ sk_C)
% 1.68/1.87        | ~ (v2_funct_1 @ sk_C))),
% 1.68/1.87      inference('sup+', [status(thm)], ['9', '90'])).
% 1.68/1.87  thf('92', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.68/1.87      inference('sup+', [status(thm)], ['17', '18'])).
% 1.68/1.87  thf(t71_relat_1, axiom,
% 1.68/1.87    (![A:$i]:
% 1.68/1.87     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.68/1.87       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.68/1.87  thf('93', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 1.68/1.87      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.68/1.87  thf('94', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 1.68/1.87      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.68/1.87  thf('95', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 1.68/1.87      inference('demod', [status(thm)], ['93', '94'])).
% 1.68/1.87  thf('96', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.68/1.87      inference('sup+', [status(thm)], ['17', '18'])).
% 1.68/1.87  thf(t80_relat_1, axiom,
% 1.68/1.87    (![A:$i]:
% 1.68/1.87     ( ( v1_relat_1 @ A ) =>
% 1.68/1.87       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 1.68/1.87  thf('97', plain,
% 1.68/1.87      (![X20 : $i]:
% 1.68/1.87         (((k5_relat_1 @ X20 @ (k6_relat_1 @ (k2_relat_1 @ X20))) = (X20))
% 1.68/1.87          | ~ (v1_relat_1 @ X20))),
% 1.68/1.87      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.68/1.87  thf('98', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 1.68/1.87      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.68/1.87  thf('99', plain,
% 1.68/1.87      (![X20 : $i]:
% 1.68/1.87         (((k5_relat_1 @ X20 @ (k6_partfun1 @ (k2_relat_1 @ X20))) = (X20))
% 1.68/1.87          | ~ (v1_relat_1 @ X20))),
% 1.68/1.87      inference('demod', [status(thm)], ['97', '98'])).
% 1.68/1.87  thf('100', plain,
% 1.68/1.87      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))
% 1.68/1.87        | ~ (v1_relat_1 @ sk_C))),
% 1.68/1.87      inference('sup+', [status(thm)], ['96', '99'])).
% 1.68/1.87  thf('101', plain, ((v1_relat_1 @ sk_C)),
% 1.68/1.87      inference('demod', [status(thm)], ['32', '33'])).
% 1.68/1.87  thf('102', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.68/1.87      inference('demod', [status(thm)], ['100', '101'])).
% 1.68/1.87  thf(t182_relat_1, axiom,
% 1.68/1.87    (![A:$i]:
% 1.68/1.87     ( ( v1_relat_1 @ A ) =>
% 1.68/1.87       ( ![B:$i]:
% 1.68/1.87         ( ( v1_relat_1 @ B ) =>
% 1.68/1.87           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.68/1.87             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 1.68/1.87  thf('103', plain,
% 1.68/1.87      (![X10 : $i, X11 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ X10)
% 1.68/1.87          | ((k1_relat_1 @ (k5_relat_1 @ X11 @ X10))
% 1.68/1.87              = (k10_relat_1 @ X11 @ (k1_relat_1 @ X10)))
% 1.68/1.87          | ~ (v1_relat_1 @ X11))),
% 1.68/1.87      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.68/1.87  thf('104', plain,
% 1.68/1.87      ((((k1_relat_1 @ sk_C)
% 1.68/1.87          = (k10_relat_1 @ sk_C @ (k1_relat_1 @ (k6_partfun1 @ sk_B))))
% 1.68/1.87        | ~ (v1_relat_1 @ sk_C)
% 1.68/1.87        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B)))),
% 1.68/1.87      inference('sup+', [status(thm)], ['102', '103'])).
% 1.68/1.87  thf('105', plain,
% 1.68/1.87      (![X17 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 1.68/1.87      inference('demod', [status(thm)], ['93', '94'])).
% 1.68/1.87  thf('106', plain, ((v1_relat_1 @ sk_C)),
% 1.68/1.87      inference('demod', [status(thm)], ['32', '33'])).
% 1.68/1.87  thf('107', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.68/1.87      inference('demod', [status(thm)], ['67', '68'])).
% 1.68/1.87  thf('108', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))),
% 1.68/1.87      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 1.68/1.87  thf('109', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.68/1.87      inference('demod', [status(thm)], ['100', '101'])).
% 1.68/1.87  thf('110', plain,
% 1.68/1.87      (![X10 : $i, X11 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ X10)
% 1.68/1.87          | ((k1_relat_1 @ (k5_relat_1 @ X11 @ X10))
% 1.68/1.87              = (k10_relat_1 @ X11 @ (k1_relat_1 @ X10)))
% 1.68/1.87          | ~ (v1_relat_1 @ X11))),
% 1.68/1.87      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.68/1.87  thf(t146_relat_1, axiom,
% 1.68/1.87    (![A:$i]:
% 1.68/1.87     ( ( v1_relat_1 @ A ) =>
% 1.68/1.87       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 1.68/1.87  thf('111', plain,
% 1.68/1.87      (![X9 : $i]:
% 1.68/1.87         (((k9_relat_1 @ X9 @ (k1_relat_1 @ X9)) = (k2_relat_1 @ X9))
% 1.68/1.87          | ~ (v1_relat_1 @ X9))),
% 1.68/1.87      inference('cnf', [status(esa)], [t146_relat_1])).
% 1.68/1.87  thf('112', plain,
% 1.68/1.87      (![X0 : $i, X1 : $i]:
% 1.68/1.87         (((k9_relat_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 1.68/1.87            (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)))
% 1.68/1.87            = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 1.68/1.87          | ~ (v1_relat_1 @ X1)
% 1.68/1.87          | ~ (v1_relat_1 @ X0)
% 1.68/1.87          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 1.68/1.87      inference('sup+', [status(thm)], ['110', '111'])).
% 1.68/1.87  thf('113', plain,
% 1.68/1.87      ((~ (v1_relat_1 @ sk_C)
% 1.68/1.87        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 1.68/1.87        | ~ (v1_relat_1 @ sk_C)
% 1.68/1.87        | ((k9_relat_1 @ (k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) @ 
% 1.68/1.87            (k10_relat_1 @ sk_C @ (k1_relat_1 @ (k6_partfun1 @ sk_B))))
% 1.68/1.87            = (k2_relat_1 @ (k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)))))),
% 1.68/1.87      inference('sup-', [status(thm)], ['109', '112'])).
% 1.68/1.87  thf('114', plain, ((v1_relat_1 @ sk_C)),
% 1.68/1.87      inference('demod', [status(thm)], ['32', '33'])).
% 1.68/1.87  thf('115', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.68/1.87      inference('demod', [status(thm)], ['67', '68'])).
% 1.68/1.87  thf('116', plain, ((v1_relat_1 @ sk_C)),
% 1.68/1.87      inference('demod', [status(thm)], ['32', '33'])).
% 1.68/1.87  thf('117', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.68/1.87      inference('demod', [status(thm)], ['100', '101'])).
% 1.68/1.87  thf('118', plain,
% 1.68/1.87      (![X17 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 1.68/1.87      inference('demod', [status(thm)], ['93', '94'])).
% 1.68/1.87  thf('119', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.68/1.87      inference('demod', [status(thm)], ['100', '101'])).
% 1.68/1.87  thf('120', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.68/1.87      inference('sup+', [status(thm)], ['17', '18'])).
% 1.68/1.87  thf('121', plain,
% 1.68/1.87      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_B)) = (sk_B))),
% 1.68/1.87      inference('demod', [status(thm)],
% 1.68/1.87                ['113', '114', '115', '116', '117', '118', '119', '120'])).
% 1.68/1.87  thf('122', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))),
% 1.68/1.87      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 1.68/1.87  thf('123', plain, (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (sk_B))),
% 1.68/1.87      inference('demod', [status(thm)], ['121', '122'])).
% 1.68/1.87  thf('124', plain, ((v1_relat_1 @ sk_C)),
% 1.68/1.87      inference('demod', [status(thm)], ['32', '33'])).
% 1.68/1.87  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('126', plain, ((v2_funct_1 @ sk_C)),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('127', plain,
% 1.68/1.87      (((sk_B) = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 1.68/1.87      inference('demod', [status(thm)],
% 1.68/1.87                ['91', '92', '95', '108', '123', '124', '125', '126'])).
% 1.68/1.87  thf(t78_relat_1, axiom,
% 1.68/1.87    (![A:$i]:
% 1.68/1.87     ( ( v1_relat_1 @ A ) =>
% 1.68/1.87       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 1.68/1.87  thf('128', plain,
% 1.68/1.87      (![X19 : $i]:
% 1.68/1.87         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X19)) @ X19) = (X19))
% 1.68/1.87          | ~ (v1_relat_1 @ X19))),
% 1.68/1.87      inference('cnf', [status(esa)], [t78_relat_1])).
% 1.68/1.87  thf('129', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 1.68/1.87      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.68/1.87  thf('130', plain,
% 1.68/1.87      (![X19 : $i]:
% 1.68/1.87         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X19)) @ X19) = (X19))
% 1.68/1.87          | ~ (v1_relat_1 @ X19))),
% 1.68/1.87      inference('demod', [status(thm)], ['128', '129'])).
% 1.68/1.87  thf('131', plain,
% 1.68/1.87      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.68/1.87          (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.68/1.87          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.68/1.87        | ~ (v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 1.68/1.87      inference('sup+', [status(thm)], ['127', '130'])).
% 1.68/1.87  thf('132', plain,
% 1.68/1.87      ((~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.68/1.87        | ~ (v1_relat_1 @ sk_C)
% 1.68/1.87        | ~ (v1_funct_1 @ sk_C)
% 1.68/1.87        | ~ (v2_funct_1 @ sk_C)
% 1.68/1.87        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.68/1.87            (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.68/1.87            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 1.68/1.87      inference('sup-', [status(thm)], ['8', '131'])).
% 1.68/1.87  thf('133', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.68/1.87      inference('sup+', [status(thm)], ['17', '18'])).
% 1.68/1.87  thf('134', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.68/1.87      inference('demod', [status(thm)], ['67', '68'])).
% 1.68/1.87  thf('135', plain, ((v1_relat_1 @ sk_C)),
% 1.68/1.87      inference('demod', [status(thm)], ['32', '33'])).
% 1.68/1.87  thf('136', plain, ((v1_funct_1 @ sk_C)),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('137', plain, ((v2_funct_1 @ sk_C)),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('138', plain,
% 1.68/1.87      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.68/1.87         (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.68/1.87         = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))),
% 1.68/1.87      inference('demod', [status(thm)],
% 1.68/1.87                ['132', '133', '134', '135', '136', '137'])).
% 1.68/1.87  thf('139', plain,
% 1.68/1.87      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.68/1.87          (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.68/1.87          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.68/1.87        | ~ (v1_relat_1 @ sk_C)
% 1.68/1.87        | ~ (v1_funct_1 @ sk_C)
% 1.68/1.87        | ~ (v2_funct_1 @ sk_C))),
% 1.68/1.87      inference('sup+', [status(thm)], ['7', '138'])).
% 1.68/1.87  thf('140', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.68/1.87      inference('sup+', [status(thm)], ['17', '18'])).
% 1.68/1.87  thf('141', plain,
% 1.68/1.87      (![X17 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 1.68/1.87      inference('demod', [status(thm)], ['93', '94'])).
% 1.68/1.87  thf('142', plain,
% 1.68/1.87      (![X19 : $i]:
% 1.68/1.87         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X19)) @ X19) = (X19))
% 1.68/1.87          | ~ (v1_relat_1 @ X19))),
% 1.68/1.87      inference('demod', [status(thm)], ['128', '129'])).
% 1.68/1.87  thf('143', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.68/1.87            = (k6_partfun1 @ X0))
% 1.68/1.87          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.68/1.87      inference('sup+', [status(thm)], ['141', '142'])).
% 1.68/1.87  thf('144', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.68/1.87      inference('demod', [status(thm)], ['67', '68'])).
% 1.68/1.87  thf('145', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.68/1.87           = (k6_partfun1 @ X0))),
% 1.68/1.87      inference('demod', [status(thm)], ['143', '144'])).
% 1.68/1.87  thf('146', plain, ((v1_relat_1 @ sk_C)),
% 1.68/1.87      inference('demod', [status(thm)], ['32', '33'])).
% 1.68/1.87  thf('147', plain, ((v1_funct_1 @ sk_C)),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('148', plain, ((v2_funct_1 @ sk_C)),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('149', plain,
% 1.68/1.87      (((k6_partfun1 @ sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))),
% 1.68/1.87      inference('demod', [status(thm)],
% 1.68/1.87                ['139', '140', '145', '146', '147', '148'])).
% 1.68/1.87  thf(t55_relat_1, axiom,
% 1.68/1.87    (![A:$i]:
% 1.68/1.87     ( ( v1_relat_1 @ A ) =>
% 1.68/1.87       ( ![B:$i]:
% 1.68/1.87         ( ( v1_relat_1 @ B ) =>
% 1.68/1.87           ( ![C:$i]:
% 1.68/1.87             ( ( v1_relat_1 @ C ) =>
% 1.68/1.87               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.68/1.87                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.68/1.87  thf('150', plain,
% 1.68/1.87      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ X14)
% 1.68/1.87          | ((k5_relat_1 @ (k5_relat_1 @ X15 @ X14) @ X16)
% 1.68/1.87              = (k5_relat_1 @ X15 @ (k5_relat_1 @ X14 @ X16)))
% 1.68/1.87          | ~ (v1_relat_1 @ X16)
% 1.68/1.87          | ~ (v1_relat_1 @ X15))),
% 1.68/1.87      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.68/1.87  thf('151', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.68/1.87            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.68/1.87          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.68/1.87          | ~ (v1_relat_1 @ X0)
% 1.68/1.87          | ~ (v1_relat_1 @ sk_C))),
% 1.68/1.87      inference('sup+', [status(thm)], ['149', '150'])).
% 1.68/1.87  thf('152', plain, ((v1_relat_1 @ sk_C)),
% 1.68/1.87      inference('demod', [status(thm)], ['32', '33'])).
% 1.68/1.87  thf('153', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.68/1.87            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.68/1.87          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.68/1.87          | ~ (v1_relat_1 @ X0))),
% 1.68/1.87      inference('demod', [status(thm)], ['151', '152'])).
% 1.68/1.87  thf('154', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ sk_C)
% 1.68/1.87          | ~ (v1_funct_1 @ sk_C)
% 1.68/1.87          | ~ (v1_relat_1 @ X0)
% 1.68/1.87          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.68/1.87              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.68/1.87      inference('sup-', [status(thm)], ['4', '153'])).
% 1.68/1.87  thf('155', plain, ((v1_relat_1 @ sk_C)),
% 1.68/1.87      inference('demod', [status(thm)], ['32', '33'])).
% 1.68/1.87  thf('156', plain, ((v1_funct_1 @ sk_C)),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('157', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ X0)
% 1.68/1.87          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.68/1.87              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.68/1.87      inference('demod', [status(thm)], ['154', '155', '156'])).
% 1.68/1.87  thf('158', plain,
% 1.68/1.87      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.68/1.87          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 1.68/1.87             (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 1.68/1.87        | ~ (v1_relat_1 @ sk_C)
% 1.68/1.87        | ~ (v1_funct_1 @ sk_C)
% 1.68/1.87        | ~ (v2_funct_1 @ sk_C)
% 1.68/1.87        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.68/1.87      inference('sup+', [status(thm)], ['3', '157'])).
% 1.68/1.87  thf('159', plain,
% 1.68/1.87      (![X21 : $i]:
% 1.68/1.87         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 1.68/1.87          | ~ (v1_funct_1 @ X21)
% 1.68/1.87          | ~ (v1_relat_1 @ X21))),
% 1.68/1.87      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.68/1.87  thf('160', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.68/1.87      inference('demod', [status(thm)], ['46', '47', '48', '49', '50', '51'])).
% 1.68/1.87  thf('161', plain,
% 1.68/1.87      (![X19 : $i]:
% 1.68/1.87         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X19)) @ X19) = (X19))
% 1.68/1.87          | ~ (v1_relat_1 @ X19))),
% 1.68/1.87      inference('demod', [status(thm)], ['128', '129'])).
% 1.68/1.87  thf('162', plain,
% 1.68/1.87      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.68/1.87          = (k2_funct_1 @ sk_C))
% 1.68/1.87        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.68/1.87      inference('sup+', [status(thm)], ['160', '161'])).
% 1.68/1.87  thf('163', plain,
% 1.68/1.87      ((~ (v1_relat_1 @ sk_C)
% 1.68/1.87        | ~ (v1_funct_1 @ sk_C)
% 1.68/1.87        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.68/1.87            = (k2_funct_1 @ sk_C)))),
% 1.68/1.87      inference('sup-', [status(thm)], ['159', '162'])).
% 1.68/1.87  thf('164', plain, ((v1_relat_1 @ sk_C)),
% 1.68/1.87      inference('demod', [status(thm)], ['32', '33'])).
% 1.68/1.87  thf('165', plain, ((v1_funct_1 @ sk_C)),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('166', plain,
% 1.68/1.87      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.68/1.87         = (k2_funct_1 @ sk_C))),
% 1.68/1.87      inference('demod', [status(thm)], ['163', '164', '165'])).
% 1.68/1.87  thf('167', plain, ((v1_relat_1 @ sk_C)),
% 1.68/1.87      inference('demod', [status(thm)], ['32', '33'])).
% 1.68/1.87  thf('168', plain, ((v1_funct_1 @ sk_C)),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('169', plain, ((v2_funct_1 @ sk_C)),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('170', plain,
% 1.68/1.87      ((((k2_funct_1 @ sk_C)
% 1.68/1.87          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 1.68/1.87             (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 1.68/1.87        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.68/1.87      inference('demod', [status(thm)], ['158', '166', '167', '168', '169'])).
% 1.68/1.87  thf('171', plain,
% 1.68/1.87      ((~ (v1_relat_1 @ sk_C)
% 1.68/1.87        | ~ (v1_funct_1 @ sk_C)
% 1.68/1.87        | ((k2_funct_1 @ sk_C)
% 1.68/1.87            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 1.68/1.87               (k6_partfun1 @ (k1_relat_1 @ sk_C)))))),
% 1.68/1.87      inference('sup-', [status(thm)], ['0', '170'])).
% 1.68/1.87  thf('172', plain, ((v1_relat_1 @ sk_C)),
% 1.68/1.87      inference('demod', [status(thm)], ['32', '33'])).
% 1.68/1.87  thf('173', plain, ((v1_funct_1 @ sk_C)),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('174', plain,
% 1.68/1.87      (((k2_funct_1 @ sk_C)
% 1.68/1.87         = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 1.68/1.87            (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 1.68/1.87      inference('demod', [status(thm)], ['171', '172', '173'])).
% 1.68/1.87  thf('175', plain,
% 1.68/1.87      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('176', plain,
% 1.68/1.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf(redefinition_k1_partfun1, axiom,
% 1.68/1.87    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.68/1.87     ( ( ( v1_funct_1 @ E ) & 
% 1.68/1.87         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.68/1.87         ( v1_funct_1 @ F ) & 
% 1.68/1.87         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.68/1.87       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.68/1.87  thf('177', plain,
% 1.68/1.87      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 1.68/1.87         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 1.68/1.87          | ~ (v1_funct_1 @ X43)
% 1.68/1.87          | ~ (v1_funct_1 @ X46)
% 1.68/1.87          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 1.68/1.87          | ((k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46)
% 1.68/1.87              = (k5_relat_1 @ X43 @ X46)))),
% 1.68/1.87      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.68/1.87  thf('178', plain,
% 1.68/1.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.68/1.87         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.68/1.87            = (k5_relat_1 @ sk_C @ X0))
% 1.68/1.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.68/1.87          | ~ (v1_funct_1 @ X0)
% 1.68/1.87          | ~ (v1_funct_1 @ sk_C))),
% 1.68/1.87      inference('sup-', [status(thm)], ['176', '177'])).
% 1.68/1.87  thf('179', plain, ((v1_funct_1 @ sk_C)),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('180', plain,
% 1.68/1.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.68/1.87         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.68/1.87            = (k5_relat_1 @ sk_C @ X0))
% 1.68/1.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.68/1.87          | ~ (v1_funct_1 @ X0))),
% 1.68/1.87      inference('demod', [status(thm)], ['178', '179'])).
% 1.68/1.87  thf('181', plain,
% 1.68/1.87      ((~ (v1_funct_1 @ sk_D)
% 1.68/1.87        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.68/1.87            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.68/1.87      inference('sup-', [status(thm)], ['175', '180'])).
% 1.68/1.87  thf('182', plain, ((v1_funct_1 @ sk_D)),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('183', plain,
% 1.68/1.87      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.68/1.87        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.68/1.87        (k6_partfun1 @ sk_A))),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('184', plain,
% 1.68/1.87      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('185', plain,
% 1.68/1.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf(dt_k1_partfun1, axiom,
% 1.68/1.87    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.68/1.87     ( ( ( v1_funct_1 @ E ) & 
% 1.68/1.87         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.68/1.87         ( v1_funct_1 @ F ) & 
% 1.68/1.87         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.68/1.87       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.68/1.87         ( m1_subset_1 @
% 1.68/1.87           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.68/1.87           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.68/1.87  thf('186', plain,
% 1.68/1.87      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 1.68/1.87         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.68/1.87          | ~ (v1_funct_1 @ X37)
% 1.68/1.87          | ~ (v1_funct_1 @ X40)
% 1.68/1.87          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 1.68/1.87          | (m1_subset_1 @ (k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40) @ 
% 1.68/1.87             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X42))))),
% 1.68/1.87      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.68/1.87  thf('187', plain,
% 1.68/1.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.68/1.87         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.68/1.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.68/1.87          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.68/1.87          | ~ (v1_funct_1 @ X1)
% 1.68/1.87          | ~ (v1_funct_1 @ sk_C))),
% 1.68/1.87      inference('sup-', [status(thm)], ['185', '186'])).
% 1.68/1.87  thf('188', plain, ((v1_funct_1 @ sk_C)),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('189', plain,
% 1.68/1.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.68/1.87         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.68/1.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.68/1.87          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.68/1.87          | ~ (v1_funct_1 @ X1))),
% 1.68/1.87      inference('demod', [status(thm)], ['187', '188'])).
% 1.68/1.87  thf('190', plain,
% 1.68/1.87      ((~ (v1_funct_1 @ sk_D)
% 1.68/1.87        | (m1_subset_1 @ 
% 1.68/1.87           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.68/1.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.68/1.87      inference('sup-', [status(thm)], ['184', '189'])).
% 1.68/1.87  thf('191', plain, ((v1_funct_1 @ sk_D)),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('192', plain,
% 1.68/1.87      ((m1_subset_1 @ 
% 1.68/1.87        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.68/1.87        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.68/1.87      inference('demod', [status(thm)], ['190', '191'])).
% 1.68/1.87  thf(redefinition_r2_relset_1, axiom,
% 1.68/1.87    (![A:$i,B:$i,C:$i,D:$i]:
% 1.68/1.87     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.68/1.87         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.68/1.87       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.68/1.87  thf('193', plain,
% 1.68/1.87      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.68/1.87         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.68/1.87          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.68/1.87          | ((X32) = (X35))
% 1.68/1.87          | ~ (r2_relset_1 @ X33 @ X34 @ X32 @ X35))),
% 1.68/1.87      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.68/1.87  thf('194', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.68/1.87             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 1.68/1.87          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 1.68/1.87          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.68/1.87      inference('sup-', [status(thm)], ['192', '193'])).
% 1.68/1.87  thf('195', plain,
% 1.68/1.87      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.68/1.87           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.68/1.87        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.68/1.87            = (k6_partfun1 @ sk_A)))),
% 1.68/1.87      inference('sup-', [status(thm)], ['183', '194'])).
% 1.68/1.87  thf('196', plain,
% 1.68/1.87      (![X36 : $i]:
% 1.68/1.87         (m1_subset_1 @ (k6_partfun1 @ X36) @ 
% 1.68/1.87          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 1.68/1.87      inference('demod', [status(thm)], ['63', '64'])).
% 1.68/1.87  thf('197', plain,
% 1.68/1.87      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.68/1.87         = (k6_partfun1 @ sk_A))),
% 1.68/1.87      inference('demod', [status(thm)], ['195', '196'])).
% 1.68/1.87  thf('198', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.68/1.87      inference('demod', [status(thm)], ['181', '182', '197'])).
% 1.68/1.87  thf('199', plain,
% 1.68/1.87      (![X12 : $i, X13 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ X12)
% 1.68/1.87          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X13 @ X12)) @ 
% 1.68/1.87             (k1_relat_1 @ X13))
% 1.68/1.87          | ~ (v1_relat_1 @ X13))),
% 1.68/1.87      inference('cnf', [status(esa)], [t44_relat_1])).
% 1.68/1.87  thf('200', plain,
% 1.68/1.87      (![X0 : $i, X2 : $i]:
% 1.68/1.87         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.68/1.87      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.68/1.87  thf('201', plain,
% 1.68/1.87      (![X0 : $i, X1 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ X0)
% 1.68/1.87          | ~ (v1_relat_1 @ X1)
% 1.68/1.87          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ 
% 1.68/1.87               (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 1.68/1.87          | ((k1_relat_1 @ X0) = (k1_relat_1 @ (k5_relat_1 @ X0 @ X1))))),
% 1.68/1.87      inference('sup-', [status(thm)], ['199', '200'])).
% 1.68/1.87  thf('202', plain,
% 1.68/1.87      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ 
% 1.68/1.87           (k1_relat_1 @ (k6_partfun1 @ sk_A)))
% 1.68/1.87        | ((k1_relat_1 @ sk_C) = (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 1.68/1.87        | ~ (v1_relat_1 @ sk_D)
% 1.68/1.87        | ~ (v1_relat_1 @ sk_C))),
% 1.68/1.87      inference('sup-', [status(thm)], ['198', '201'])).
% 1.68/1.87  thf('203', plain,
% 1.68/1.87      (![X17 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 1.68/1.87      inference('demod', [status(thm)], ['93', '94'])).
% 1.68/1.87  thf('204', plain,
% 1.68/1.87      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf(cc2_relset_1, axiom,
% 1.68/1.87    (![A:$i,B:$i,C:$i]:
% 1.68/1.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.68/1.87       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.68/1.87  thf('205', plain,
% 1.68/1.87      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.68/1.87         ((v4_relat_1 @ X26 @ X27)
% 1.68/1.87          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.68/1.87      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.68/1.87  thf('206', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 1.68/1.87      inference('sup-', [status(thm)], ['204', '205'])).
% 1.68/1.87  thf('207', plain,
% 1.68/1.87      (![X5 : $i, X6 : $i]:
% 1.68/1.87         (~ (v4_relat_1 @ X5 @ X6)
% 1.68/1.87          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.68/1.87          | ~ (v1_relat_1 @ X5))),
% 1.68/1.87      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.68/1.87  thf('208', plain,
% 1.68/1.87      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 1.68/1.87      inference('sup-', [status(thm)], ['206', '207'])).
% 1.68/1.87  thf('209', plain, ((v1_relat_1 @ sk_C)),
% 1.68/1.87      inference('demod', [status(thm)], ['32', '33'])).
% 1.68/1.87  thf('210', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 1.68/1.87      inference('demod', [status(thm)], ['208', '209'])).
% 1.68/1.87  thf('211', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.68/1.87      inference('demod', [status(thm)], ['181', '182', '197'])).
% 1.68/1.87  thf('212', plain,
% 1.68/1.87      (![X17 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 1.68/1.87      inference('demod', [status(thm)], ['93', '94'])).
% 1.68/1.87  thf('213', plain,
% 1.68/1.87      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('214', plain,
% 1.68/1.87      (![X3 : $i, X4 : $i]:
% 1.68/1.87         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.68/1.87          | (v1_relat_1 @ X3)
% 1.68/1.87          | ~ (v1_relat_1 @ X4))),
% 1.68/1.87      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.68/1.87  thf('215', plain,
% 1.68/1.87      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.68/1.87      inference('sup-', [status(thm)], ['213', '214'])).
% 1.68/1.87  thf('216', plain,
% 1.68/1.87      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 1.68/1.87      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.68/1.87  thf('217', plain, ((v1_relat_1 @ sk_D)),
% 1.68/1.87      inference('demod', [status(thm)], ['215', '216'])).
% 1.68/1.87  thf('218', plain, ((v1_relat_1 @ sk_C)),
% 1.68/1.87      inference('demod', [status(thm)], ['32', '33'])).
% 1.68/1.87  thf('219', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 1.68/1.87      inference('demod', [status(thm)],
% 1.68/1.87                ['202', '203', '210', '211', '212', '217', '218'])).
% 1.68/1.87  thf('220', plain,
% 1.68/1.87      (((k2_funct_1 @ sk_C)
% 1.68/1.87         = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))),
% 1.68/1.87      inference('demod', [status(thm)], ['174', '219'])).
% 1.68/1.87  thf('221', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.68/1.87      inference('demod', [status(thm)], ['181', '182', '197'])).
% 1.68/1.87  thf('222', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ X0)
% 1.68/1.87          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.68/1.87              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.68/1.87      inference('demod', [status(thm)], ['154', '155', '156'])).
% 1.68/1.87  thf('223', plain,
% 1.68/1.87      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.68/1.87          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 1.68/1.87        | ~ (v1_relat_1 @ sk_D))),
% 1.68/1.87      inference('sup+', [status(thm)], ['221', '222'])).
% 1.68/1.87  thf('224', plain, ((v1_relat_1 @ sk_D)),
% 1.68/1.87      inference('demod', [status(thm)], ['215', '216'])).
% 1.68/1.87  thf('225', plain,
% 1.68/1.87      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.68/1.87         = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))),
% 1.68/1.87      inference('demod', [status(thm)], ['223', '224'])).
% 1.68/1.87  thf('226', plain,
% 1.68/1.87      (![X20 : $i]:
% 1.68/1.87         (((k5_relat_1 @ X20 @ (k6_partfun1 @ (k2_relat_1 @ X20))) = (X20))
% 1.68/1.87          | ~ (v1_relat_1 @ X20))),
% 1.68/1.87      inference('demod', [status(thm)], ['97', '98'])).
% 1.68/1.87  thf('227', plain,
% 1.68/1.87      (![X10 : $i, X11 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ X10)
% 1.68/1.87          | ((k1_relat_1 @ (k5_relat_1 @ X11 @ X10))
% 1.68/1.87              = (k10_relat_1 @ X11 @ (k1_relat_1 @ X10)))
% 1.68/1.87          | ~ (v1_relat_1 @ X11))),
% 1.68/1.87      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.68/1.87  thf('228', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         (((k1_relat_1 @ X0)
% 1.68/1.87            = (k10_relat_1 @ X0 @ 
% 1.68/1.87               (k1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))
% 1.68/1.87          | ~ (v1_relat_1 @ X0)
% 1.68/1.87          | ~ (v1_relat_1 @ X0)
% 1.68/1.87          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 1.68/1.87      inference('sup+', [status(thm)], ['226', '227'])).
% 1.68/1.87  thf('229', plain,
% 1.68/1.87      (![X17 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 1.68/1.87      inference('demod', [status(thm)], ['93', '94'])).
% 1.68/1.87  thf('230', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.68/1.87      inference('demod', [status(thm)], ['67', '68'])).
% 1.68/1.87  thf('231', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         (((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 1.68/1.87          | ~ (v1_relat_1 @ X0)
% 1.68/1.87          | ~ (v1_relat_1 @ X0))),
% 1.68/1.87      inference('demod', [status(thm)], ['228', '229', '230'])).
% 1.68/1.87  thf('232', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ X0)
% 1.68/1.87          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 1.68/1.87      inference('simplify', [status(thm)], ['231'])).
% 1.68/1.87  thf('233', plain,
% 1.68/1.87      (![X10 : $i, X11 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ X10)
% 1.68/1.87          | ((k1_relat_1 @ (k5_relat_1 @ X11 @ X10))
% 1.68/1.87              = (k10_relat_1 @ X11 @ (k1_relat_1 @ X10)))
% 1.68/1.87          | ~ (v1_relat_1 @ X11))),
% 1.68/1.87      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.68/1.87  thf('234', plain,
% 1.68/1.87      (![X20 : $i]:
% 1.68/1.87         (((k5_relat_1 @ X20 @ (k6_partfun1 @ (k2_relat_1 @ X20))) = (X20))
% 1.68/1.87          | ~ (v1_relat_1 @ X20))),
% 1.68/1.87      inference('demod', [status(thm)], ['97', '98'])).
% 1.68/1.87  thf('235', plain,
% 1.68/1.87      (![X19 : $i]:
% 1.68/1.87         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X19)) @ X19) = (X19))
% 1.68/1.87          | ~ (v1_relat_1 @ X19))),
% 1.68/1.87      inference('demod', [status(thm)], ['128', '129'])).
% 1.68/1.87  thf('236', plain,
% 1.68/1.87      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ X14)
% 1.68/1.87          | ((k5_relat_1 @ (k5_relat_1 @ X15 @ X14) @ X16)
% 1.68/1.87              = (k5_relat_1 @ X15 @ (k5_relat_1 @ X14 @ X16)))
% 1.68/1.87          | ~ (v1_relat_1 @ X16)
% 1.68/1.87          | ~ (v1_relat_1 @ X15))),
% 1.68/1.87      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.68/1.87  thf('237', plain,
% 1.68/1.87      (![X0 : $i, X1 : $i]:
% 1.68/1.87         (((k5_relat_1 @ X0 @ X1)
% 1.68/1.87            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 1.68/1.87               (k5_relat_1 @ X0 @ X1)))
% 1.68/1.87          | ~ (v1_relat_1 @ X0)
% 1.68/1.87          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.68/1.87          | ~ (v1_relat_1 @ X1)
% 1.68/1.87          | ~ (v1_relat_1 @ X0))),
% 1.68/1.87      inference('sup+', [status(thm)], ['235', '236'])).
% 1.68/1.87  thf('238', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.68/1.87      inference('demod', [status(thm)], ['67', '68'])).
% 1.68/1.87  thf('239', plain,
% 1.68/1.87      (![X0 : $i, X1 : $i]:
% 1.68/1.87         (((k5_relat_1 @ X0 @ X1)
% 1.68/1.87            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 1.68/1.87               (k5_relat_1 @ X0 @ X1)))
% 1.68/1.87          | ~ (v1_relat_1 @ X0)
% 1.68/1.87          | ~ (v1_relat_1 @ X1)
% 1.68/1.87          | ~ (v1_relat_1 @ X0))),
% 1.68/1.87      inference('demod', [status(thm)], ['237', '238'])).
% 1.68/1.87  thf('240', plain,
% 1.68/1.87      (![X0 : $i, X1 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ X1)
% 1.68/1.87          | ~ (v1_relat_1 @ X0)
% 1.68/1.87          | ((k5_relat_1 @ X0 @ X1)
% 1.68/1.87              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 1.68/1.87                 (k5_relat_1 @ X0 @ X1))))),
% 1.68/1.87      inference('simplify', [status(thm)], ['239'])).
% 1.68/1.87  thf('241', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         (((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.68/1.87            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 1.68/1.87          | ~ (v1_relat_1 @ X0)
% 1.68/1.87          | ~ (v1_relat_1 @ X0)
% 1.68/1.87          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 1.68/1.87      inference('sup+', [status(thm)], ['234', '240'])).
% 1.68/1.87  thf('242', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.68/1.87      inference('demod', [status(thm)], ['67', '68'])).
% 1.68/1.87  thf('243', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         (((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.68/1.87            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 1.68/1.87          | ~ (v1_relat_1 @ X0)
% 1.68/1.87          | ~ (v1_relat_1 @ X0))),
% 1.68/1.87      inference('demod', [status(thm)], ['241', '242'])).
% 1.68/1.87  thf('244', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ X0)
% 1.68/1.87          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.68/1.87              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0)))),
% 1.68/1.87      inference('simplify', [status(thm)], ['243'])).
% 1.68/1.87  thf('245', plain,
% 1.68/1.87      (![X19 : $i]:
% 1.68/1.87         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X19)) @ X19) = (X19))
% 1.68/1.87          | ~ (v1_relat_1 @ X19))),
% 1.68/1.87      inference('demod', [status(thm)], ['128', '129'])).
% 1.68/1.87  thf('246', plain,
% 1.68/1.87      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('247', plain,
% 1.68/1.87      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.68/1.87         ((v4_relat_1 @ X26 @ X27)
% 1.68/1.87          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.68/1.87      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.68/1.87  thf('248', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 1.68/1.87      inference('sup-', [status(thm)], ['246', '247'])).
% 1.68/1.87  thf('249', plain,
% 1.68/1.87      (![X5 : $i, X6 : $i]:
% 1.68/1.87         (~ (v4_relat_1 @ X5 @ X6)
% 1.68/1.87          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.68/1.87          | ~ (v1_relat_1 @ X5))),
% 1.68/1.87      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.68/1.87  thf('250', plain,
% 1.68/1.87      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 1.68/1.87      inference('sup-', [status(thm)], ['248', '249'])).
% 1.68/1.87  thf('251', plain, ((v1_relat_1 @ sk_D)),
% 1.68/1.87      inference('demod', [status(thm)], ['215', '216'])).
% 1.68/1.87  thf('252', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 1.68/1.87      inference('demod', [status(thm)], ['250', '251'])).
% 1.68/1.87  thf('253', plain,
% 1.68/1.87      (![X19 : $i]:
% 1.68/1.87         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X19)) @ X19) = (X19))
% 1.68/1.87          | ~ (v1_relat_1 @ X19))),
% 1.68/1.87      inference('demod', [status(thm)], ['128', '129'])).
% 1.68/1.87  thf('254', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.68/1.87           = (k6_partfun1 @ X0))),
% 1.68/1.87      inference('demod', [status(thm)], ['143', '144'])).
% 1.68/1.87  thf('255', plain,
% 1.68/1.87      (![X10 : $i, X11 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ X10)
% 1.68/1.87          | ((k1_relat_1 @ (k5_relat_1 @ X11 @ X10))
% 1.68/1.87              = (k10_relat_1 @ X11 @ (k1_relat_1 @ X10)))
% 1.68/1.87          | ~ (v1_relat_1 @ X11))),
% 1.68/1.87      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.68/1.87  thf('256', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         (((k1_relat_1 @ (k6_partfun1 @ X0))
% 1.68/1.87            = (k10_relat_1 @ (k6_partfun1 @ X0) @ 
% 1.68/1.87               (k1_relat_1 @ (k6_partfun1 @ X0))))
% 1.68/1.87          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.68/1.87          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.68/1.87      inference('sup+', [status(thm)], ['254', '255'])).
% 1.68/1.87  thf('257', plain,
% 1.68/1.87      (![X17 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 1.68/1.87      inference('demod', [status(thm)], ['93', '94'])).
% 1.68/1.87  thf('258', plain,
% 1.68/1.87      (![X17 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 1.68/1.87      inference('demod', [status(thm)], ['93', '94'])).
% 1.68/1.87  thf('259', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.68/1.87      inference('demod', [status(thm)], ['67', '68'])).
% 1.68/1.87  thf('260', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.68/1.87      inference('demod', [status(thm)], ['67', '68'])).
% 1.68/1.87  thf('261', plain,
% 1.68/1.87      (![X0 : $i]: ((X0) = (k10_relat_1 @ (k6_partfun1 @ X0) @ X0))),
% 1.68/1.87      inference('demod', [status(thm)], ['256', '257', '258', '259', '260'])).
% 1.68/1.87  thf('262', plain,
% 1.68/1.87      (![X10 : $i, X11 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ X10)
% 1.68/1.87          | ((k1_relat_1 @ (k5_relat_1 @ X11 @ X10))
% 1.68/1.87              = (k10_relat_1 @ X11 @ (k1_relat_1 @ X10)))
% 1.68/1.87          | ~ (v1_relat_1 @ X11))),
% 1.68/1.87      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.68/1.87  thf('263', plain,
% 1.68/1.87      (![X5 : $i, X6 : $i]:
% 1.68/1.87         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.68/1.87          | (v4_relat_1 @ X5 @ X6)
% 1.68/1.87          | ~ (v1_relat_1 @ X5))),
% 1.68/1.87      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.68/1.87  thf('264', plain,
% 1.68/1.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.68/1.87         (~ (r1_tarski @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ X2)
% 1.68/1.87          | ~ (v1_relat_1 @ X1)
% 1.68/1.87          | ~ (v1_relat_1 @ X0)
% 1.68/1.87          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.68/1.87          | (v4_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2))),
% 1.68/1.87      inference('sup-', [status(thm)], ['262', '263'])).
% 1.68/1.87  thf('265', plain,
% 1.68/1.87      (![X0 : $i, X1 : $i]:
% 1.68/1.87         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.68/1.87          | (v4_relat_1 @ 
% 1.68/1.87             (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0) @ X1)
% 1.68/1.87          | ~ (v1_relat_1 @ 
% 1.68/1.87               (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 1.68/1.87          | ~ (v1_relat_1 @ X0)
% 1.68/1.87          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0))))),
% 1.68/1.87      inference('sup-', [status(thm)], ['261', '264'])).
% 1.68/1.87  thf('266', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.68/1.87      inference('demod', [status(thm)], ['67', '68'])).
% 1.68/1.87  thf('267', plain,
% 1.68/1.87      (![X0 : $i, X1 : $i]:
% 1.68/1.87         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.68/1.87          | (v4_relat_1 @ 
% 1.68/1.87             (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0) @ X1)
% 1.68/1.87          | ~ (v1_relat_1 @ 
% 1.68/1.87               (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0))
% 1.68/1.87          | ~ (v1_relat_1 @ X0))),
% 1.68/1.87      inference('demod', [status(thm)], ['265', '266'])).
% 1.68/1.87  thf('268', plain,
% 1.68/1.87      (![X0 : $i, X1 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ X0)
% 1.68/1.87          | ~ (v1_relat_1 @ X0)
% 1.68/1.87          | ~ (v1_relat_1 @ X0)
% 1.68/1.87          | (v4_relat_1 @ 
% 1.68/1.87             (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0) @ X1)
% 1.68/1.87          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ X1))),
% 1.68/1.87      inference('sup-', [status(thm)], ['253', '267'])).
% 1.68/1.87  thf('269', plain,
% 1.68/1.87      (![X0 : $i, X1 : $i]:
% 1.68/1.87         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.68/1.87          | (v4_relat_1 @ 
% 1.68/1.87             (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0) @ X1)
% 1.68/1.87          | ~ (v1_relat_1 @ X0))),
% 1.68/1.87      inference('simplify', [status(thm)], ['268'])).
% 1.68/1.87  thf('270', plain,
% 1.68/1.87      ((~ (v1_relat_1 @ sk_D)
% 1.68/1.87        | (v4_relat_1 @ 
% 1.68/1.87           (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D) @ sk_B))),
% 1.68/1.87      inference('sup-', [status(thm)], ['252', '269'])).
% 1.68/1.87  thf('271', plain, ((v1_relat_1 @ sk_D)),
% 1.68/1.87      inference('demod', [status(thm)], ['215', '216'])).
% 1.68/1.87  thf('272', plain,
% 1.68/1.87      ((v4_relat_1 @ 
% 1.68/1.87        (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D) @ sk_B)),
% 1.68/1.87      inference('demod', [status(thm)], ['270', '271'])).
% 1.68/1.87  thf('273', plain,
% 1.68/1.87      (![X5 : $i, X6 : $i]:
% 1.68/1.87         (~ (v4_relat_1 @ X5 @ X6)
% 1.68/1.87          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.68/1.87          | ~ (v1_relat_1 @ X5))),
% 1.68/1.87      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.68/1.87  thf('274', plain,
% 1.68/1.87      ((~ (v1_relat_1 @ 
% 1.68/1.87           (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D))
% 1.68/1.87        | (r1_tarski @ 
% 1.68/1.87           (k1_relat_1 @ 
% 1.68/1.87            (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D)) @ 
% 1.68/1.87           sk_B))),
% 1.68/1.87      inference('sup-', [status(thm)], ['272', '273'])).
% 1.68/1.87  thf('275', plain,
% 1.68/1.87      ((~ (v1_relat_1 @ sk_D)
% 1.68/1.87        | ~ (v1_relat_1 @ sk_D)
% 1.68/1.87        | (r1_tarski @ 
% 1.68/1.87           (k1_relat_1 @ 
% 1.68/1.87            (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D)) @ 
% 1.68/1.87           sk_B))),
% 1.68/1.87      inference('sup-', [status(thm)], ['245', '274'])).
% 1.68/1.87  thf('276', plain, ((v1_relat_1 @ sk_D)),
% 1.68/1.87      inference('demod', [status(thm)], ['215', '216'])).
% 1.68/1.87  thf('277', plain, ((v1_relat_1 @ sk_D)),
% 1.68/1.87      inference('demod', [status(thm)], ['215', '216'])).
% 1.68/1.87  thf('278', plain,
% 1.68/1.87      ((r1_tarski @ 
% 1.68/1.87        (k1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D)) @ 
% 1.68/1.87        sk_B)),
% 1.68/1.87      inference('demod', [status(thm)], ['275', '276', '277'])).
% 1.68/1.87  thf('279', plain,
% 1.68/1.87      (((r1_tarski @ 
% 1.68/1.87         (k1_relat_1 @ 
% 1.68/1.87          (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D)))) @ 
% 1.68/1.87         sk_B)
% 1.68/1.87        | ~ (v1_relat_1 @ sk_D))),
% 1.68/1.87      inference('sup+', [status(thm)], ['244', '278'])).
% 1.68/1.87  thf('280', plain, ((v1_relat_1 @ sk_D)),
% 1.68/1.87      inference('demod', [status(thm)], ['215', '216'])).
% 1.68/1.87  thf('281', plain,
% 1.68/1.87      ((r1_tarski @ 
% 1.68/1.87        (k1_relat_1 @ (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D)))) @ 
% 1.68/1.87        sk_B)),
% 1.68/1.87      inference('demod', [status(thm)], ['279', '280'])).
% 1.68/1.87  thf('282', plain,
% 1.68/1.87      (((r1_tarski @ 
% 1.68/1.87         (k10_relat_1 @ sk_D @ 
% 1.68/1.87          (k1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_D)))) @ 
% 1.68/1.87         sk_B)
% 1.68/1.87        | ~ (v1_relat_1 @ sk_D)
% 1.68/1.87        | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))),
% 1.68/1.87      inference('sup+', [status(thm)], ['233', '281'])).
% 1.68/1.87  thf('283', plain,
% 1.68/1.87      (![X17 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 1.68/1.87      inference('demod', [status(thm)], ['93', '94'])).
% 1.68/1.87  thf('284', plain, ((v1_relat_1 @ sk_D)),
% 1.68/1.87      inference('demod', [status(thm)], ['215', '216'])).
% 1.68/1.87  thf('285', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.68/1.87      inference('demod', [status(thm)], ['67', '68'])).
% 1.68/1.87  thf('286', plain,
% 1.68/1.87      ((r1_tarski @ (k10_relat_1 @ sk_D @ (k2_relat_1 @ sk_D)) @ sk_B)),
% 1.68/1.87      inference('demod', [status(thm)], ['282', '283', '284', '285'])).
% 1.68/1.87  thf('287', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         (~ (r1_tarski @ X0 @ sk_B)
% 1.68/1.87          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 1.68/1.87      inference('demod', [status(thm)], ['86', '87', '88'])).
% 1.68/1.87  thf('288', plain,
% 1.68/1.87      (((k9_relat_1 @ sk_C @ 
% 1.68/1.87         (k10_relat_1 @ sk_C @ (k10_relat_1 @ sk_D @ (k2_relat_1 @ sk_D))))
% 1.68/1.87         = (k10_relat_1 @ sk_D @ (k2_relat_1 @ sk_D)))),
% 1.68/1.87      inference('sup-', [status(thm)], ['286', '287'])).
% 1.68/1.87  thf('289', plain,
% 1.68/1.87      ((((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 1.68/1.87          = (k10_relat_1 @ sk_D @ (k2_relat_1 @ sk_D)))
% 1.68/1.87        | ~ (v1_relat_1 @ sk_D))),
% 1.68/1.87      inference('sup+', [status(thm)], ['232', '288'])).
% 1.68/1.87  thf('290', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 1.68/1.87      inference('demod', [status(thm)], ['250', '251'])).
% 1.68/1.87  thf('291', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         (~ (r1_tarski @ X0 @ sk_B)
% 1.68/1.87          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 1.68/1.87      inference('demod', [status(thm)], ['86', '87', '88'])).
% 1.68/1.87  thf('292', plain,
% 1.68/1.87      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 1.68/1.87         = (k1_relat_1 @ sk_D))),
% 1.68/1.87      inference('sup-', [status(thm)], ['290', '291'])).
% 1.68/1.87  thf('293', plain, ((v1_relat_1 @ sk_D)),
% 1.68/1.87      inference('demod', [status(thm)], ['215', '216'])).
% 1.68/1.87  thf('294', plain,
% 1.68/1.87      (((k1_relat_1 @ sk_D) = (k10_relat_1 @ sk_D @ (k2_relat_1 @ sk_D)))),
% 1.68/1.87      inference('demod', [status(thm)], ['289', '292', '293'])).
% 1.68/1.87  thf('295', plain,
% 1.68/1.87      (![X20 : $i]:
% 1.68/1.87         (((k5_relat_1 @ X20 @ (k6_partfun1 @ (k2_relat_1 @ X20))) = (X20))
% 1.68/1.87          | ~ (v1_relat_1 @ X20))),
% 1.68/1.87      inference('demod', [status(thm)], ['97', '98'])).
% 1.68/1.87  thf('296', plain,
% 1.68/1.87      (![X10 : $i, X11 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ X10)
% 1.68/1.87          | ((k1_relat_1 @ (k5_relat_1 @ X11 @ X10))
% 1.68/1.87              = (k10_relat_1 @ X11 @ (k1_relat_1 @ X10)))
% 1.68/1.87          | ~ (v1_relat_1 @ X11))),
% 1.68/1.87      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.68/1.87  thf('297', plain,
% 1.68/1.87      (![X19 : $i]:
% 1.68/1.87         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X19)) @ X19) = (X19))
% 1.68/1.87          | ~ (v1_relat_1 @ X19))),
% 1.68/1.87      inference('demod', [status(thm)], ['128', '129'])).
% 1.68/1.87  thf('298', plain,
% 1.68/1.87      (![X0 : $i, X1 : $i]:
% 1.68/1.87         (((k5_relat_1 @ 
% 1.68/1.87            (k6_partfun1 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0))) @ 
% 1.68/1.87            (k5_relat_1 @ X1 @ X0)) = (k5_relat_1 @ X1 @ X0))
% 1.68/1.87          | ~ (v1_relat_1 @ X1)
% 1.68/1.87          | ~ (v1_relat_1 @ X0)
% 1.68/1.87          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 1.68/1.87      inference('sup+', [status(thm)], ['296', '297'])).
% 1.68/1.87  thf('299', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ X0)
% 1.68/1.87          | ~ (v1_relat_1 @ X0)
% 1.68/1.87          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 1.68/1.87          | ~ (v1_relat_1 @ X0)
% 1.68/1.87          | ((k5_relat_1 @ 
% 1.68/1.87              (k6_partfun1 @ 
% 1.68/1.87               (k10_relat_1 @ X0 @ 
% 1.68/1.87                (k1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0))))) @ 
% 1.68/1.87              (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 1.68/1.87              = (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))),
% 1.68/1.87      inference('sup-', [status(thm)], ['295', '298'])).
% 1.68/1.87  thf('300', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.68/1.87      inference('demod', [status(thm)], ['67', '68'])).
% 1.68/1.87  thf('301', plain,
% 1.68/1.87      (![X17 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 1.68/1.87      inference('demod', [status(thm)], ['93', '94'])).
% 1.68/1.87  thf('302', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ X0)
% 1.68/1.87          | ~ (v1_relat_1 @ X0)
% 1.68/1.87          | ~ (v1_relat_1 @ X0)
% 1.68/1.87          | ((k5_relat_1 @ 
% 1.68/1.87              (k6_partfun1 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))) @ 
% 1.68/1.87              (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 1.68/1.87              = (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))),
% 1.68/1.87      inference('demod', [status(thm)], ['299', '300', '301'])).
% 1.68/1.87  thf('303', plain,
% 1.68/1.87      (![X0 : $i]:
% 1.68/1.87         (((k5_relat_1 @ 
% 1.68/1.87            (k6_partfun1 @ (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))) @ 
% 1.68/1.87            (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 1.68/1.87            = (k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0))))
% 1.68/1.87          | ~ (v1_relat_1 @ X0))),
% 1.68/1.87      inference('simplify', [status(thm)], ['302'])).
% 1.68/1.87  thf('304', plain,
% 1.68/1.87      ((((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ 
% 1.68/1.87          (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))
% 1.68/1.87          = (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))
% 1.68/1.87        | ~ (v1_relat_1 @ sk_D))),
% 1.68/1.87      inference('sup+', [status(thm)], ['294', '303'])).
% 1.68/1.87  thf('305', plain, ((v1_relat_1 @ sk_D)),
% 1.68/1.87      inference('demod', [status(thm)], ['215', '216'])).
% 1.68/1.87  thf('306', plain,
% 1.68/1.87      (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ 
% 1.68/1.87         (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))
% 1.68/1.87         = (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))),
% 1.68/1.87      inference('demod', [status(thm)], ['304', '305'])).
% 1.68/1.87  thf('307', plain,
% 1.68/1.87      (![X19 : $i]:
% 1.68/1.87         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X19)) @ X19) = (X19))
% 1.68/1.87          | ~ (v1_relat_1 @ X19))),
% 1.68/1.87      inference('demod', [status(thm)], ['128', '129'])).
% 1.68/1.87  thf('308', plain,
% 1.68/1.87      (![X20 : $i]:
% 1.68/1.87         (((k5_relat_1 @ X20 @ (k6_partfun1 @ (k2_relat_1 @ X20))) = (X20))
% 1.68/1.87          | ~ (v1_relat_1 @ X20))),
% 1.68/1.87      inference('demod', [status(thm)], ['97', '98'])).
% 1.68/1.87  thf('309', plain,
% 1.68/1.87      (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ 
% 1.68/1.87         (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))
% 1.68/1.87         = (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))),
% 1.68/1.87      inference('demod', [status(thm)], ['304', '305'])).
% 1.68/1.87  thf('310', plain,
% 1.68/1.87      ((((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D)
% 1.68/1.87          = (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))
% 1.68/1.87        | ~ (v1_relat_1 @ sk_D))),
% 1.68/1.87      inference('sup+', [status(thm)], ['308', '309'])).
% 1.68/1.87  thf('311', plain, ((v1_relat_1 @ sk_D)),
% 1.68/1.87      inference('demod', [status(thm)], ['215', '216'])).
% 1.68/1.87  thf('312', plain,
% 1.68/1.87      (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D)
% 1.68/1.87         = (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))),
% 1.68/1.87      inference('demod', [status(thm)], ['310', '311'])).
% 1.68/1.87  thf('313', plain,
% 1.68/1.87      ((((sk_D) = (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))
% 1.68/1.87        | ~ (v1_relat_1 @ sk_D))),
% 1.68/1.87      inference('sup+', [status(thm)], ['307', '312'])).
% 1.68/1.87  thf('314', plain, ((v1_relat_1 @ sk_D)),
% 1.68/1.87      inference('demod', [status(thm)], ['215', '216'])).
% 1.68/1.87  thf('315', plain,
% 1.68/1.87      (((sk_D) = (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))),
% 1.68/1.87      inference('demod', [status(thm)], ['313', '314'])).
% 1.68/1.87  thf('316', plain,
% 1.68/1.87      (((sk_D) = (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))),
% 1.68/1.87      inference('demod', [status(thm)], ['313', '314'])).
% 1.68/1.87  thf('317', plain,
% 1.68/1.87      (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D) = (sk_D))),
% 1.68/1.87      inference('demod', [status(thm)], ['306', '315', '316'])).
% 1.68/1.87  thf('318', plain,
% 1.68/1.87      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 1.68/1.87         = (k1_relat_1 @ sk_D))),
% 1.68/1.87      inference('sup-', [status(thm)], ['290', '291'])).
% 1.68/1.87  thf('319', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.68/1.87      inference('demod', [status(thm)], ['181', '182', '197'])).
% 1.68/1.87  thf('320', plain,
% 1.68/1.87      (![X10 : $i, X11 : $i]:
% 1.68/1.87         (~ (v1_relat_1 @ X10)
% 1.68/1.87          | ((k1_relat_1 @ (k5_relat_1 @ X11 @ X10))
% 1.68/1.87              = (k10_relat_1 @ X11 @ (k1_relat_1 @ X10)))
% 1.68/1.87          | ~ (v1_relat_1 @ X11))),
% 1.68/1.87      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.68/1.87  thf('321', plain,
% 1.68/1.87      ((((k1_relat_1 @ (k6_partfun1 @ sk_A))
% 1.68/1.87          = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 1.68/1.87        | ~ (v1_relat_1 @ sk_C)
% 1.68/1.87        | ~ (v1_relat_1 @ sk_D))),
% 1.68/1.87      inference('sup+', [status(thm)], ['319', '320'])).
% 1.68/1.87  thf('322', plain,
% 1.68/1.87      (![X17 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 1.68/1.87      inference('demod', [status(thm)], ['93', '94'])).
% 1.68/1.87  thf('323', plain, ((v1_relat_1 @ sk_C)),
% 1.68/1.87      inference('demod', [status(thm)], ['32', '33'])).
% 1.68/1.87  thf('324', plain, ((v1_relat_1 @ sk_D)),
% 1.68/1.87      inference('demod', [status(thm)], ['215', '216'])).
% 1.68/1.87  thf('325', plain, (((sk_A) = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))),
% 1.68/1.87      inference('demod', [status(thm)], ['321', '322', '323', '324'])).
% 1.68/1.87  thf('326', plain, (((k9_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_D))),
% 1.68/1.87      inference('demod', [status(thm)], ['318', '325'])).
% 1.68/1.87  thf('327', plain, (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)) = (sk_B))),
% 1.68/1.87      inference('demod', [status(thm)], ['121', '122'])).
% 1.68/1.87  thf('328', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 1.68/1.87      inference('demod', [status(thm)],
% 1.68/1.87                ['202', '203', '210', '211', '212', '217', '218'])).
% 1.68/1.87  thf('329', plain, (((k9_relat_1 @ sk_C @ sk_A) = (sk_B))),
% 1.68/1.87      inference('demod', [status(thm)], ['327', '328'])).
% 1.68/1.87  thf('330', plain, (((k1_relat_1 @ sk_D) = (sk_B))),
% 1.68/1.87      inference('sup+', [status(thm)], ['326', '329'])).
% 1.68/1.87  thf('331', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 1.68/1.87      inference('demod', [status(thm)], ['317', '330'])).
% 1.68/1.87  thf('332', plain,
% 1.68/1.87      (((sk_D) = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))),
% 1.68/1.87      inference('demod', [status(thm)], ['225', '331'])).
% 1.68/1.87  thf('333', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 1.68/1.87      inference('sup+', [status(thm)], ['220', '332'])).
% 1.68/1.87  thf('334', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.68/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.68/1.87  thf('335', plain, ($false),
% 1.68/1.87      inference('simplify_reflect-', [status(thm)], ['333', '334'])).
% 1.68/1.87  
% 1.68/1.87  % SZS output end Refutation
% 1.68/1.87  
% 1.68/1.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
