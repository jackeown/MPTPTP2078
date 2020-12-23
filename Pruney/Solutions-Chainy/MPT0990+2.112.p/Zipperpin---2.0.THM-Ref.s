%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.y4jWXPXS9T

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:13 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  271 (1974 expanded)
%              Number of leaves         :   47 ( 628 expanded)
%              Depth                    :   33
%              Number of atoms          : 2209 (35338 expanded)
%              Number of equality atoms :  133 (2286 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k5_relat_1 @ X23 @ ( k2_funct_1 @ X23 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
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
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k5_relat_1 @ X23 @ ( k2_funct_1 @ X23 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('5',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X23 ) @ X23 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('6',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('7',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X23 ) @ X23 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X22: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relat_1 @ X22 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('11',plain,(
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

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('14',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('18',plain,(
    ! [X22: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relat_1 @ X22 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('30',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['26','31','32','33'])).

thf('35',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['11','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('39',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['10','42'])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf('45',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47','48'])).

thf('50',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('51',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X19 ) @ X18 )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('52',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('53',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X19 ) @ X18 )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['49','54'])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('58',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('60',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) @ X15 )
        = ( k5_relat_1 @ X14 @ ( k5_relat_1 @ X13 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('62',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('63',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['7','71'])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('74',plain,(
    ! [X17: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('75',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('76',plain,(
    ! [X17: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('77',plain,(
    ! [X20: $i] :
      ( ( ( k5_relat_1 @ X20 @ ( k6_relat_1 @ ( k2_relat_1 @ X20 ) ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('78',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('79',plain,(
    ! [X20: $i] :
      ( ( ( k5_relat_1 @ X20 @ ( k6_partfun1 @ ( k2_relat_1 @ X20 ) ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('87',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['72','73','82','83','84','85','86'])).

thf('88',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) @ X15 )
        = ( k5_relat_1 @ X14 @ ( k5_relat_1 @ X13 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('94',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['3','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('100',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('101',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('103',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('106',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('108',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['103','108'])).

thf('110',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X19 ) @ X18 )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('111',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['106','107'])).

thf('113',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['14','15'])).

thf('115',plain,(
    ! [X20: $i] :
      ( ( ( k5_relat_1 @ X20 @ ( k6_partfun1 @ ( k2_relat_1 @ X20 ) ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('116',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('118',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) @ X15 )
        = ( k5_relat_1 @ X14 @ ( k5_relat_1 @ X13 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('120',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
        = ( k10_relat_1 @ X12 @ ( k1_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 ) ) )
        = ( k10_relat_1 @ ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['118','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('125',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['116','117'])).

thf('126',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('127',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 ) ) )
        = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['123','124','125','126','127'])).

thf('129',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
      = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['113','128'])).

thf('130',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['106','107'])).

thf('131',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
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

thf('134',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( ( k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45 )
        = ( k5_relat_1 @ X42 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('135',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['132','137'])).

thf('139',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
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

thf('143',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['141','146'])).

thf('148',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('150',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( X30 = X33 )
      | ~ ( r2_relset_1 @ X31 @ X32 @ X30 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['140','151'])).

thf('153',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('154',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['138','139','154'])).

thf('156',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('157',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('158',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( sk_A
    = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['131','155','158'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('160',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X9 @ X10 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('161',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k10_relat_1 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A )
    | ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['159','162'])).

thf('164',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('166',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('168',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('170',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,
    ( sk_A
    = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['131','155','158'])).

thf('172',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('173',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['163','170','171','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('175',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('176',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    ! [X21: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('179',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k5_relat_1 @ X23 @ ( k2_funct_1 @ X23 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('180',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['168','169'])).

thf('181',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X19 ) @ X18 )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('182',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C )
      = sk_C ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('184',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) @ X15 )
        = ( k5_relat_1 @ X14 @ ( k5_relat_1 @ X13 @ X15 ) ) )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('188',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['186','187','188'])).

thf('190',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['179','189'])).

thf('191',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['168','169'])).

thf('192',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('193',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X19 ) @ X18 )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['191','196'])).

thf('198',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('199',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['190','197','198','199','200'])).

thf('202',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['178','201'])).

thf('203',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('204',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['202','203','204'])).

thf('206',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['163','170','171','172'])).

thf('207',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['205','206'])).

thf('208',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['138','139','154'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('210',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['208','209'])).

thf('211',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['111','112'])).

thf('212',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['106','107'])).

thf('213',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['210','211','212'])).

thf('214',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('215',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('216',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['98','173','174','175','176','177','207','213','214','215'])).

thf('217',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['216','217'])).

thf('219',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','218'])).

thf('220',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('221',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    $false ),
    inference(demod,[status(thm)],['219','220','221'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.y4jWXPXS9T
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:47:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.20/1.39  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.20/1.39  % Solved by: fo/fo7.sh
% 1.20/1.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.20/1.39  % done 1342 iterations in 0.926s
% 1.20/1.39  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.20/1.39  % SZS output start Refutation
% 1.20/1.39  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.20/1.39  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.20/1.39  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.20/1.39  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.20/1.39  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.20/1.39  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.20/1.39  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.20/1.39  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.20/1.39  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.20/1.39  thf(sk_C_type, type, sk_C: $i).
% 1.20/1.39  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.20/1.39  thf(sk_B_type, type, sk_B: $i).
% 1.20/1.39  thf(sk_A_type, type, sk_A: $i).
% 1.20/1.39  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.20/1.39  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.20/1.39  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.20/1.39  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.20/1.39  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.20/1.39  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.20/1.39  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.20/1.39  thf(sk_D_type, type, sk_D: $i).
% 1.20/1.39  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.20/1.39  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.20/1.39  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.20/1.39  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.20/1.39  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.20/1.39  thf(dt_k2_funct_1, axiom,
% 1.20/1.39    (![A:$i]:
% 1.20/1.39     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.20/1.39       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.20/1.39         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.20/1.39  thf('0', plain,
% 1.20/1.39      (![X21 : $i]:
% 1.20/1.39         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 1.20/1.39          | ~ (v1_funct_1 @ X21)
% 1.20/1.39          | ~ (v1_relat_1 @ X21))),
% 1.20/1.39      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.39  thf(t61_funct_1, axiom,
% 1.20/1.39    (![A:$i]:
% 1.20/1.39     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.20/1.39       ( ( v2_funct_1 @ A ) =>
% 1.20/1.39         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.20/1.39             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.20/1.39           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.20/1.39             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.20/1.39  thf('1', plain,
% 1.20/1.39      (![X23 : $i]:
% 1.20/1.39         (~ (v2_funct_1 @ X23)
% 1.20/1.39          | ((k5_relat_1 @ X23 @ (k2_funct_1 @ X23))
% 1.20/1.39              = (k6_relat_1 @ (k1_relat_1 @ X23)))
% 1.20/1.39          | ~ (v1_funct_1 @ X23)
% 1.20/1.39          | ~ (v1_relat_1 @ X23))),
% 1.20/1.39      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.20/1.39  thf(redefinition_k6_partfun1, axiom,
% 1.20/1.39    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.20/1.39  thf('2', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 1.20/1.39      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.39  thf('3', plain,
% 1.20/1.39      (![X23 : $i]:
% 1.20/1.39         (~ (v2_funct_1 @ X23)
% 1.20/1.39          | ((k5_relat_1 @ X23 @ (k2_funct_1 @ X23))
% 1.20/1.39              = (k6_partfun1 @ (k1_relat_1 @ X23)))
% 1.20/1.39          | ~ (v1_funct_1 @ X23)
% 1.20/1.39          | ~ (v1_relat_1 @ X23))),
% 1.20/1.39      inference('demod', [status(thm)], ['1', '2'])).
% 1.20/1.39  thf('4', plain,
% 1.20/1.39      (![X21 : $i]:
% 1.20/1.39         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 1.20/1.39          | ~ (v1_funct_1 @ X21)
% 1.20/1.39          | ~ (v1_relat_1 @ X21))),
% 1.20/1.39      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.39  thf('5', plain,
% 1.20/1.39      (![X23 : $i]:
% 1.20/1.39         (~ (v2_funct_1 @ X23)
% 1.20/1.39          | ((k5_relat_1 @ (k2_funct_1 @ X23) @ X23)
% 1.20/1.39              = (k6_relat_1 @ (k2_relat_1 @ X23)))
% 1.20/1.39          | ~ (v1_funct_1 @ X23)
% 1.20/1.39          | ~ (v1_relat_1 @ X23))),
% 1.20/1.39      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.20/1.39  thf('6', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 1.20/1.39      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.39  thf('7', plain,
% 1.20/1.39      (![X23 : $i]:
% 1.20/1.39         (~ (v2_funct_1 @ X23)
% 1.20/1.39          | ((k5_relat_1 @ (k2_funct_1 @ X23) @ X23)
% 1.20/1.39              = (k6_partfun1 @ (k2_relat_1 @ X23)))
% 1.20/1.39          | ~ (v1_funct_1 @ X23)
% 1.20/1.39          | ~ (v1_relat_1 @ X23))),
% 1.20/1.39      inference('demod', [status(thm)], ['5', '6'])).
% 1.20/1.39  thf('8', plain,
% 1.20/1.39      (![X21 : $i]:
% 1.20/1.39         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 1.20/1.39          | ~ (v1_funct_1 @ X21)
% 1.20/1.39          | ~ (v1_relat_1 @ X21))),
% 1.20/1.39      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.39  thf('9', plain,
% 1.20/1.39      (![X21 : $i]:
% 1.20/1.39         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 1.20/1.39          | ~ (v1_funct_1 @ X21)
% 1.20/1.39          | ~ (v1_relat_1 @ X21))),
% 1.20/1.39      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.39  thf(t55_funct_1, axiom,
% 1.20/1.39    (![A:$i]:
% 1.20/1.39     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.20/1.39       ( ( v2_funct_1 @ A ) =>
% 1.20/1.39         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.20/1.39           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.20/1.39  thf('10', plain,
% 1.20/1.39      (![X22 : $i]:
% 1.20/1.39         (~ (v2_funct_1 @ X22)
% 1.20/1.39          | ((k2_relat_1 @ X22) = (k1_relat_1 @ (k2_funct_1 @ X22)))
% 1.20/1.39          | ~ (v1_funct_1 @ X22)
% 1.20/1.39          | ~ (v1_relat_1 @ X22))),
% 1.20/1.39      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.20/1.39  thf('11', plain,
% 1.20/1.39      (![X21 : $i]:
% 1.20/1.39         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 1.20/1.39          | ~ (v1_funct_1 @ X21)
% 1.20/1.39          | ~ (v1_relat_1 @ X21))),
% 1.20/1.39      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.39  thf(t36_funct_2, conjecture,
% 1.20/1.39    (![A:$i,B:$i,C:$i]:
% 1.20/1.39     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.20/1.39         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.20/1.39       ( ![D:$i]:
% 1.20/1.39         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.20/1.39             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.20/1.39           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.20/1.39               ( r2_relset_1 @
% 1.20/1.39                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.20/1.39                 ( k6_partfun1 @ A ) ) & 
% 1.20/1.39               ( v2_funct_1 @ C ) ) =>
% 1.20/1.39             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.20/1.39               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.20/1.39  thf(zf_stmt_0, negated_conjecture,
% 1.20/1.39    (~( ![A:$i,B:$i,C:$i]:
% 1.20/1.39        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.20/1.39            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.20/1.39          ( ![D:$i]:
% 1.20/1.39            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.20/1.39                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.20/1.39              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.20/1.39                  ( r2_relset_1 @
% 1.20/1.39                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.20/1.39                    ( k6_partfun1 @ A ) ) & 
% 1.20/1.39                  ( v2_funct_1 @ C ) ) =>
% 1.20/1.39                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.20/1.39                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.20/1.39    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.20/1.39  thf('12', plain,
% 1.20/1.39      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf(redefinition_k2_relset_1, axiom,
% 1.20/1.39    (![A:$i,B:$i,C:$i]:
% 1.20/1.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.20/1.39       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.20/1.39  thf('13', plain,
% 1.20/1.39      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.20/1.39         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 1.20/1.39          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 1.20/1.39      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.20/1.39  thf('14', plain,
% 1.20/1.39      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.20/1.39      inference('sup-', [status(thm)], ['12', '13'])).
% 1.20/1.39  thf('15', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('16', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.20/1.39      inference('sup+', [status(thm)], ['14', '15'])).
% 1.20/1.39  thf('17', plain,
% 1.20/1.39      (![X21 : $i]:
% 1.20/1.39         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 1.20/1.39          | ~ (v1_funct_1 @ X21)
% 1.20/1.39          | ~ (v1_relat_1 @ X21))),
% 1.20/1.39      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.39  thf('18', plain,
% 1.20/1.39      (![X22 : $i]:
% 1.20/1.39         (~ (v2_funct_1 @ X22)
% 1.20/1.39          | ((k2_relat_1 @ X22) = (k1_relat_1 @ (k2_funct_1 @ X22)))
% 1.20/1.39          | ~ (v1_funct_1 @ X22)
% 1.20/1.39          | ~ (v1_relat_1 @ X22))),
% 1.20/1.39      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.20/1.39  thf(d10_xboole_0, axiom,
% 1.20/1.39    (![A:$i,B:$i]:
% 1.20/1.39     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.20/1.39  thf('19', plain,
% 1.20/1.39      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.20/1.39      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.20/1.39  thf('20', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.20/1.39      inference('simplify', [status(thm)], ['19'])).
% 1.20/1.39  thf(d18_relat_1, axiom,
% 1.20/1.39    (![A:$i,B:$i]:
% 1.20/1.39     ( ( v1_relat_1 @ B ) =>
% 1.20/1.39       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.20/1.39  thf('21', plain,
% 1.20/1.39      (![X5 : $i, X6 : $i]:
% 1.20/1.39         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.20/1.39          | (v4_relat_1 @ X5 @ X6)
% 1.20/1.39          | ~ (v1_relat_1 @ X5))),
% 1.20/1.39      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.20/1.39  thf('22', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 1.20/1.39      inference('sup-', [status(thm)], ['20', '21'])).
% 1.20/1.39  thf('23', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.20/1.39          | ~ (v1_relat_1 @ X0)
% 1.20/1.39          | ~ (v1_funct_1 @ X0)
% 1.20/1.39          | ~ (v2_funct_1 @ X0)
% 1.20/1.39          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.20/1.39      inference('sup+', [status(thm)], ['18', '22'])).
% 1.20/1.39  thf('24', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (~ (v1_relat_1 @ X0)
% 1.20/1.39          | ~ (v1_funct_1 @ X0)
% 1.20/1.39          | ~ (v2_funct_1 @ X0)
% 1.20/1.39          | ~ (v1_funct_1 @ X0)
% 1.20/1.39          | ~ (v1_relat_1 @ X0)
% 1.20/1.39          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.20/1.39      inference('sup-', [status(thm)], ['17', '23'])).
% 1.20/1.39  thf('25', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.20/1.39          | ~ (v2_funct_1 @ X0)
% 1.20/1.39          | ~ (v1_funct_1 @ X0)
% 1.20/1.39          | ~ (v1_relat_1 @ X0))),
% 1.20/1.39      inference('simplify', [status(thm)], ['24'])).
% 1.20/1.39  thf('26', plain,
% 1.20/1.39      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 1.20/1.39        | ~ (v1_relat_1 @ sk_C)
% 1.20/1.39        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.39        | ~ (v2_funct_1 @ sk_C))),
% 1.20/1.39      inference('sup+', [status(thm)], ['16', '25'])).
% 1.20/1.39  thf('27', plain,
% 1.20/1.39      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf(cc2_relat_1, axiom,
% 1.20/1.39    (![A:$i]:
% 1.20/1.39     ( ( v1_relat_1 @ A ) =>
% 1.20/1.39       ( ![B:$i]:
% 1.20/1.39         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.20/1.39  thf('28', plain,
% 1.20/1.39      (![X3 : $i, X4 : $i]:
% 1.20/1.39         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.20/1.39          | (v1_relat_1 @ X3)
% 1.20/1.39          | ~ (v1_relat_1 @ X4))),
% 1.20/1.39      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.20/1.39  thf('29', plain,
% 1.20/1.39      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 1.20/1.39      inference('sup-', [status(thm)], ['27', '28'])).
% 1.20/1.39  thf(fc6_relat_1, axiom,
% 1.20/1.39    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.20/1.39  thf('30', plain,
% 1.20/1.39      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 1.20/1.39      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.20/1.39  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.39      inference('demod', [status(thm)], ['29', '30'])).
% 1.20/1.39  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('33', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('34', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 1.20/1.39      inference('demod', [status(thm)], ['26', '31', '32', '33'])).
% 1.20/1.39  thf('35', plain,
% 1.20/1.39      (![X5 : $i, X6 : $i]:
% 1.20/1.39         (~ (v4_relat_1 @ X5 @ X6)
% 1.20/1.39          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.20/1.39          | ~ (v1_relat_1 @ X5))),
% 1.20/1.39      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.20/1.39  thf('36', plain,
% 1.20/1.39      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.39        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.20/1.39      inference('sup-', [status(thm)], ['34', '35'])).
% 1.20/1.39  thf('37', plain,
% 1.20/1.39      ((~ (v1_relat_1 @ sk_C)
% 1.20/1.39        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.39        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.20/1.39      inference('sup-', [status(thm)], ['11', '36'])).
% 1.20/1.39  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.39      inference('demod', [status(thm)], ['29', '30'])).
% 1.20/1.39  thf('39', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('40', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 1.20/1.39      inference('demod', [status(thm)], ['37', '38', '39'])).
% 1.20/1.39  thf('41', plain,
% 1.20/1.39      (![X0 : $i, X2 : $i]:
% 1.20/1.39         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.20/1.39      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.20/1.39  thf('42', plain,
% 1.20/1.39      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.20/1.39        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.20/1.39      inference('sup-', [status(thm)], ['40', '41'])).
% 1.20/1.39  thf('43', plain,
% 1.20/1.39      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 1.20/1.39        | ~ (v1_relat_1 @ sk_C)
% 1.20/1.39        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.39        | ~ (v2_funct_1 @ sk_C)
% 1.20/1.39        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.20/1.39      inference('sup-', [status(thm)], ['10', '42'])).
% 1.20/1.39  thf('44', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.20/1.39      inference('sup+', [status(thm)], ['14', '15'])).
% 1.20/1.39  thf('45', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.20/1.39      inference('simplify', [status(thm)], ['19'])).
% 1.20/1.39  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.39      inference('demod', [status(thm)], ['29', '30'])).
% 1.20/1.39  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('48', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('49', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.39      inference('demod', [status(thm)], ['43', '44', '45', '46', '47', '48'])).
% 1.20/1.39  thf('50', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.20/1.39      inference('simplify', [status(thm)], ['19'])).
% 1.20/1.39  thf(t77_relat_1, axiom,
% 1.20/1.39    (![A:$i,B:$i]:
% 1.20/1.39     ( ( v1_relat_1 @ B ) =>
% 1.20/1.39       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 1.20/1.39         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 1.20/1.39  thf('51', plain,
% 1.20/1.39      (![X18 : $i, X19 : $i]:
% 1.20/1.39         (~ (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 1.20/1.39          | ((k5_relat_1 @ (k6_relat_1 @ X19) @ X18) = (X18))
% 1.20/1.39          | ~ (v1_relat_1 @ X18))),
% 1.20/1.39      inference('cnf', [status(esa)], [t77_relat_1])).
% 1.20/1.39  thf('52', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 1.20/1.39      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.39  thf('53', plain,
% 1.20/1.39      (![X18 : $i, X19 : $i]:
% 1.20/1.39         (~ (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 1.20/1.39          | ((k5_relat_1 @ (k6_partfun1 @ X19) @ X18) = (X18))
% 1.20/1.39          | ~ (v1_relat_1 @ X18))),
% 1.20/1.39      inference('demod', [status(thm)], ['51', '52'])).
% 1.20/1.39  thf('54', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (~ (v1_relat_1 @ X0)
% 1.20/1.39          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 1.20/1.39      inference('sup-', [status(thm)], ['50', '53'])).
% 1.20/1.39  thf('55', plain,
% 1.20/1.39      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.20/1.39          = (k2_funct_1 @ sk_C))
% 1.20/1.39        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.39      inference('sup+', [status(thm)], ['49', '54'])).
% 1.20/1.39  thf('56', plain,
% 1.20/1.39      ((~ (v1_relat_1 @ sk_C)
% 1.20/1.39        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.39        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.20/1.39            = (k2_funct_1 @ sk_C)))),
% 1.20/1.39      inference('sup-', [status(thm)], ['9', '55'])).
% 1.20/1.39  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.39      inference('demod', [status(thm)], ['29', '30'])).
% 1.20/1.39  thf('58', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('59', plain,
% 1.20/1.39      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.20/1.39         = (k2_funct_1 @ sk_C))),
% 1.20/1.39      inference('demod', [status(thm)], ['56', '57', '58'])).
% 1.20/1.39  thf(t55_relat_1, axiom,
% 1.20/1.39    (![A:$i]:
% 1.20/1.39     ( ( v1_relat_1 @ A ) =>
% 1.20/1.39       ( ![B:$i]:
% 1.20/1.39         ( ( v1_relat_1 @ B ) =>
% 1.20/1.39           ( ![C:$i]:
% 1.20/1.39             ( ( v1_relat_1 @ C ) =>
% 1.20/1.39               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.20/1.39                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.20/1.39  thf('60', plain,
% 1.20/1.39      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.20/1.39         (~ (v1_relat_1 @ X13)
% 1.20/1.39          | ((k5_relat_1 @ (k5_relat_1 @ X14 @ X13) @ X15)
% 1.20/1.39              = (k5_relat_1 @ X14 @ (k5_relat_1 @ X13 @ X15)))
% 1.20/1.39          | ~ (v1_relat_1 @ X15)
% 1.20/1.39          | ~ (v1_relat_1 @ X14))),
% 1.20/1.39      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.20/1.39  thf('61', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 1.20/1.39            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.20/1.39               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 1.20/1.39          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 1.20/1.39          | ~ (v1_relat_1 @ X0)
% 1.20/1.39          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.39      inference('sup+', [status(thm)], ['59', '60'])).
% 1.20/1.39  thf(dt_k6_partfun1, axiom,
% 1.20/1.39    (![A:$i]:
% 1.20/1.39     ( ( m1_subset_1 @
% 1.20/1.39         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.20/1.39       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.20/1.39  thf('62', plain,
% 1.20/1.39      (![X41 : $i]:
% 1.20/1.39         (m1_subset_1 @ (k6_partfun1 @ X41) @ 
% 1.20/1.39          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 1.20/1.39      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.20/1.39  thf('63', plain,
% 1.20/1.39      (![X3 : $i, X4 : $i]:
% 1.20/1.39         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.20/1.39          | (v1_relat_1 @ X3)
% 1.20/1.39          | ~ (v1_relat_1 @ X4))),
% 1.20/1.39      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.20/1.39  thf('64', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X0))
% 1.20/1.39          | (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.20/1.39      inference('sup-', [status(thm)], ['62', '63'])).
% 1.20/1.39  thf('65', plain,
% 1.20/1.39      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 1.20/1.39      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.20/1.39  thf('66', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.20/1.39      inference('demod', [status(thm)], ['64', '65'])).
% 1.20/1.39  thf('67', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 1.20/1.39            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.20/1.39               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 1.20/1.39          | ~ (v1_relat_1 @ X0)
% 1.20/1.39          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.39      inference('demod', [status(thm)], ['61', '66'])).
% 1.20/1.39  thf('68', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (~ (v1_relat_1 @ sk_C)
% 1.20/1.39          | ~ (v1_funct_1 @ sk_C)
% 1.20/1.39          | ~ (v1_relat_1 @ X0)
% 1.20/1.39          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 1.20/1.39              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.20/1.39                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 1.20/1.39      inference('sup-', [status(thm)], ['8', '67'])).
% 1.20/1.39  thf('69', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.39      inference('demod', [status(thm)], ['29', '30'])).
% 1.20/1.39  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('71', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (~ (v1_relat_1 @ X0)
% 1.20/1.39          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 1.20/1.39              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.20/1.39                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 1.20/1.39      inference('demod', [status(thm)], ['68', '69', '70'])).
% 1.20/1.39  thf('72', plain,
% 1.20/1.39      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 1.20/1.39          = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.20/1.39             (k6_partfun1 @ (k2_relat_1 @ sk_C))))
% 1.20/1.39        | ~ (v1_relat_1 @ sk_C)
% 1.20/1.39        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.39        | ~ (v2_funct_1 @ sk_C)
% 1.20/1.39        | ~ (v1_relat_1 @ sk_C))),
% 1.20/1.39      inference('sup+', [status(thm)], ['7', '71'])).
% 1.20/1.39  thf('73', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.20/1.39      inference('sup+', [status(thm)], ['14', '15'])).
% 1.20/1.39  thf(t71_relat_1, axiom,
% 1.20/1.39    (![A:$i]:
% 1.20/1.39     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.20/1.39       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.20/1.39  thf('74', plain, (![X17 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 1.20/1.39      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.20/1.39  thf('75', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 1.20/1.39      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.39  thf('76', plain, (![X17 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 1.20/1.39      inference('demod', [status(thm)], ['74', '75'])).
% 1.20/1.39  thf(t80_relat_1, axiom,
% 1.20/1.39    (![A:$i]:
% 1.20/1.39     ( ( v1_relat_1 @ A ) =>
% 1.20/1.39       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 1.20/1.39  thf('77', plain,
% 1.20/1.39      (![X20 : $i]:
% 1.20/1.39         (((k5_relat_1 @ X20 @ (k6_relat_1 @ (k2_relat_1 @ X20))) = (X20))
% 1.20/1.39          | ~ (v1_relat_1 @ X20))),
% 1.20/1.39      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.20/1.39  thf('78', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 1.20/1.39      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.39  thf('79', plain,
% 1.20/1.39      (![X20 : $i]:
% 1.20/1.39         (((k5_relat_1 @ X20 @ (k6_partfun1 @ (k2_relat_1 @ X20))) = (X20))
% 1.20/1.39          | ~ (v1_relat_1 @ X20))),
% 1.20/1.39      inference('demod', [status(thm)], ['77', '78'])).
% 1.20/1.39  thf('80', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.20/1.39            = (k6_partfun1 @ X0))
% 1.20/1.39          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.20/1.39      inference('sup+', [status(thm)], ['76', '79'])).
% 1.20/1.39  thf('81', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.20/1.39      inference('demod', [status(thm)], ['64', '65'])).
% 1.20/1.39  thf('82', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.20/1.39           = (k6_partfun1 @ X0))),
% 1.20/1.39      inference('demod', [status(thm)], ['80', '81'])).
% 1.20/1.39  thf('83', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.39      inference('demod', [status(thm)], ['29', '30'])).
% 1.20/1.39  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('85', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('86', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.39      inference('demod', [status(thm)], ['29', '30'])).
% 1.20/1.39  thf('87', plain,
% 1.20/1.39      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 1.20/1.39      inference('demod', [status(thm)],
% 1.20/1.39                ['72', '73', '82', '83', '84', '85', '86'])).
% 1.20/1.39  thf('88', plain,
% 1.20/1.39      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.20/1.39         (~ (v1_relat_1 @ X13)
% 1.20/1.39          | ((k5_relat_1 @ (k5_relat_1 @ X14 @ X13) @ X15)
% 1.20/1.39              = (k5_relat_1 @ X14 @ (k5_relat_1 @ X13 @ X15)))
% 1.20/1.39          | ~ (v1_relat_1 @ X15)
% 1.20/1.39          | ~ (v1_relat_1 @ X14))),
% 1.20/1.39      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.20/1.39  thf('89', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.20/1.39            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.20/1.39          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.39          | ~ (v1_relat_1 @ X0)
% 1.20/1.39          | ~ (v1_relat_1 @ sk_C))),
% 1.20/1.39      inference('sup+', [status(thm)], ['87', '88'])).
% 1.20/1.39  thf('90', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.39      inference('demod', [status(thm)], ['29', '30'])).
% 1.20/1.39  thf('91', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.20/1.39            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.20/1.39          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.39          | ~ (v1_relat_1 @ X0))),
% 1.20/1.39      inference('demod', [status(thm)], ['89', '90'])).
% 1.20/1.39  thf('92', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (~ (v1_relat_1 @ sk_C)
% 1.20/1.39          | ~ (v1_funct_1 @ sk_C)
% 1.20/1.39          | ~ (v1_relat_1 @ X0)
% 1.20/1.39          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.20/1.39              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.20/1.39      inference('sup-', [status(thm)], ['4', '91'])).
% 1.20/1.39  thf('93', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.39      inference('demod', [status(thm)], ['29', '30'])).
% 1.20/1.39  thf('94', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('95', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (~ (v1_relat_1 @ X0)
% 1.20/1.39          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.20/1.39              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.20/1.39      inference('demod', [status(thm)], ['92', '93', '94'])).
% 1.20/1.39  thf('96', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (~ (v1_relat_1 @ X0)
% 1.20/1.39          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 1.20/1.39              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.20/1.39                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 1.20/1.39      inference('demod', [status(thm)], ['68', '69', '70'])).
% 1.20/1.39  thf('97', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))
% 1.20/1.39            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.20/1.39               (k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)))
% 1.20/1.39          | ~ (v1_relat_1 @ X0)
% 1.20/1.39          | ~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ X0)))),
% 1.20/1.39      inference('sup+', [status(thm)], ['95', '96'])).
% 1.20/1.39  thf('98', plain,
% 1.20/1.39      ((~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 1.20/1.39        | ~ (v1_relat_1 @ sk_C)
% 1.20/1.39        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.39        | ~ (v2_funct_1 @ sk_C)
% 1.20/1.39        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.20/1.39        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 1.20/1.39            (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 1.20/1.39            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.20/1.39               (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)))))),
% 1.20/1.39      inference('sup-', [status(thm)], ['3', '97'])).
% 1.20/1.39  thf('99', plain,
% 1.20/1.39      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf(cc2_relset_1, axiom,
% 1.20/1.39    (![A:$i,B:$i,C:$i]:
% 1.20/1.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.20/1.39       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.20/1.39  thf('100', plain,
% 1.20/1.39      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.20/1.39         ((v4_relat_1 @ X24 @ X25)
% 1.20/1.39          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.20/1.39      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.20/1.39  thf('101', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 1.20/1.39      inference('sup-', [status(thm)], ['99', '100'])).
% 1.20/1.39  thf('102', plain,
% 1.20/1.39      (![X5 : $i, X6 : $i]:
% 1.20/1.39         (~ (v4_relat_1 @ X5 @ X6)
% 1.20/1.39          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.20/1.39          | ~ (v1_relat_1 @ X5))),
% 1.20/1.39      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.20/1.39  thf('103', plain,
% 1.20/1.39      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 1.20/1.39      inference('sup-', [status(thm)], ['101', '102'])).
% 1.20/1.39  thf('104', plain,
% 1.20/1.39      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('105', plain,
% 1.20/1.39      (![X3 : $i, X4 : $i]:
% 1.20/1.39         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.20/1.39          | (v1_relat_1 @ X3)
% 1.20/1.39          | ~ (v1_relat_1 @ X4))),
% 1.20/1.39      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.20/1.39  thf('106', plain,
% 1.20/1.39      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.20/1.39      inference('sup-', [status(thm)], ['104', '105'])).
% 1.20/1.39  thf('107', plain,
% 1.20/1.39      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 1.20/1.39      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.20/1.39  thf('108', plain, ((v1_relat_1 @ sk_D)),
% 1.20/1.39      inference('demod', [status(thm)], ['106', '107'])).
% 1.20/1.39  thf('109', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 1.20/1.39      inference('demod', [status(thm)], ['103', '108'])).
% 1.20/1.39  thf('110', plain,
% 1.20/1.39      (![X18 : $i, X19 : $i]:
% 1.20/1.39         (~ (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 1.20/1.39          | ((k5_relat_1 @ (k6_partfun1 @ X19) @ X18) = (X18))
% 1.20/1.39          | ~ (v1_relat_1 @ X18))),
% 1.20/1.39      inference('demod', [status(thm)], ['51', '52'])).
% 1.20/1.39  thf('111', plain,
% 1.20/1.39      ((~ (v1_relat_1 @ sk_D)
% 1.20/1.39        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D)))),
% 1.20/1.39      inference('sup-', [status(thm)], ['109', '110'])).
% 1.20/1.39  thf('112', plain, ((v1_relat_1 @ sk_D)),
% 1.20/1.39      inference('demod', [status(thm)], ['106', '107'])).
% 1.20/1.39  thf('113', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 1.20/1.39      inference('demod', [status(thm)], ['111', '112'])).
% 1.20/1.39  thf('114', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.20/1.39      inference('sup+', [status(thm)], ['14', '15'])).
% 1.20/1.39  thf('115', plain,
% 1.20/1.39      (![X20 : $i]:
% 1.20/1.39         (((k5_relat_1 @ X20 @ (k6_partfun1 @ (k2_relat_1 @ X20))) = (X20))
% 1.20/1.39          | ~ (v1_relat_1 @ X20))),
% 1.20/1.39      inference('demod', [status(thm)], ['77', '78'])).
% 1.20/1.39  thf('116', plain,
% 1.20/1.39      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))
% 1.20/1.39        | ~ (v1_relat_1 @ sk_C))),
% 1.20/1.39      inference('sup+', [status(thm)], ['114', '115'])).
% 1.20/1.39  thf('117', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.39      inference('demod', [status(thm)], ['29', '30'])).
% 1.20/1.39  thf('118', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.20/1.39      inference('demod', [status(thm)], ['116', '117'])).
% 1.20/1.39  thf('119', plain,
% 1.20/1.39      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.20/1.39         (~ (v1_relat_1 @ X13)
% 1.20/1.39          | ((k5_relat_1 @ (k5_relat_1 @ X14 @ X13) @ X15)
% 1.20/1.39              = (k5_relat_1 @ X14 @ (k5_relat_1 @ X13 @ X15)))
% 1.20/1.39          | ~ (v1_relat_1 @ X15)
% 1.20/1.39          | ~ (v1_relat_1 @ X14))),
% 1.20/1.39      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.20/1.39  thf(t182_relat_1, axiom,
% 1.20/1.39    (![A:$i]:
% 1.20/1.39     ( ( v1_relat_1 @ A ) =>
% 1.20/1.39       ( ![B:$i]:
% 1.20/1.39         ( ( v1_relat_1 @ B ) =>
% 1.20/1.39           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.20/1.39             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 1.20/1.39  thf('120', plain,
% 1.20/1.39      (![X11 : $i, X12 : $i]:
% 1.20/1.39         (~ (v1_relat_1 @ X11)
% 1.20/1.39          | ((k1_relat_1 @ (k5_relat_1 @ X12 @ X11))
% 1.20/1.39              = (k10_relat_1 @ X12 @ (k1_relat_1 @ X11)))
% 1.20/1.39          | ~ (v1_relat_1 @ X12))),
% 1.20/1.39      inference('cnf', [status(esa)], [t182_relat_1])).
% 1.20/1.39  thf('121', plain,
% 1.20/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.39         (((k1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 1.20/1.39            = (k10_relat_1 @ (k5_relat_1 @ X2 @ X1) @ (k1_relat_1 @ X0)))
% 1.20/1.39          | ~ (v1_relat_1 @ X2)
% 1.20/1.39          | ~ (v1_relat_1 @ X0)
% 1.20/1.39          | ~ (v1_relat_1 @ X1)
% 1.20/1.39          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 1.20/1.39          | ~ (v1_relat_1 @ X0))),
% 1.20/1.39      inference('sup+', [status(thm)], ['119', '120'])).
% 1.20/1.39  thf('122', plain,
% 1.20/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.39         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 1.20/1.39          | ~ (v1_relat_1 @ X1)
% 1.20/1.39          | ~ (v1_relat_1 @ X0)
% 1.20/1.39          | ~ (v1_relat_1 @ X2)
% 1.20/1.39          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 1.20/1.39              = (k10_relat_1 @ (k5_relat_1 @ X2 @ X1) @ (k1_relat_1 @ X0))))),
% 1.20/1.39      inference('simplify', [status(thm)], ['121'])).
% 1.20/1.39  thf('123', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (~ (v1_relat_1 @ sk_C)
% 1.20/1.39          | ((k1_relat_1 @ 
% 1.20/1.39              (k5_relat_1 @ sk_C @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)))
% 1.20/1.39              = (k10_relat_1 @ (k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) @ 
% 1.20/1.39                 (k1_relat_1 @ X0)))
% 1.20/1.39          | ~ (v1_relat_1 @ sk_C)
% 1.20/1.39          | ~ (v1_relat_1 @ X0)
% 1.20/1.39          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B)))),
% 1.20/1.39      inference('sup-', [status(thm)], ['118', '122'])).
% 1.20/1.39  thf('124', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.39      inference('demod', [status(thm)], ['29', '30'])).
% 1.20/1.39  thf('125', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.20/1.39      inference('demod', [status(thm)], ['116', '117'])).
% 1.20/1.39  thf('126', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.39      inference('demod', [status(thm)], ['29', '30'])).
% 1.20/1.39  thf('127', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.20/1.39      inference('demod', [status(thm)], ['64', '65'])).
% 1.20/1.39  thf('128', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (((k1_relat_1 @ 
% 1.20/1.39            (k5_relat_1 @ sk_C @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)))
% 1.20/1.39            = (k10_relat_1 @ sk_C @ (k1_relat_1 @ X0)))
% 1.20/1.39          | ~ (v1_relat_1 @ X0))),
% 1.20/1.39      inference('demod', [status(thm)], ['123', '124', '125', '126', '127'])).
% 1.20/1.39  thf('129', plain,
% 1.20/1.39      ((((k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 1.20/1.39          = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 1.20/1.39        | ~ (v1_relat_1 @ sk_D))),
% 1.20/1.39      inference('sup+', [status(thm)], ['113', '128'])).
% 1.20/1.39  thf('130', plain, ((v1_relat_1 @ sk_D)),
% 1.20/1.39      inference('demod', [status(thm)], ['106', '107'])).
% 1.20/1.39  thf('131', plain,
% 1.20/1.39      (((k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 1.20/1.39         = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))),
% 1.20/1.39      inference('demod', [status(thm)], ['129', '130'])).
% 1.20/1.39  thf('132', plain,
% 1.20/1.39      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('133', plain,
% 1.20/1.39      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf(redefinition_k1_partfun1, axiom,
% 1.20/1.39    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.20/1.39     ( ( ( v1_funct_1 @ E ) & 
% 1.20/1.39         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.20/1.39         ( v1_funct_1 @ F ) & 
% 1.20/1.39         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.20/1.39       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.20/1.39  thf('134', plain,
% 1.20/1.39      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 1.20/1.39         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 1.20/1.39          | ~ (v1_funct_1 @ X42)
% 1.20/1.39          | ~ (v1_funct_1 @ X45)
% 1.20/1.39          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 1.20/1.39          | ((k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45)
% 1.20/1.39              = (k5_relat_1 @ X42 @ X45)))),
% 1.20/1.39      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.20/1.39  thf('135', plain,
% 1.20/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.39         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.20/1.39            = (k5_relat_1 @ sk_C @ X0))
% 1.20/1.39          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.20/1.39          | ~ (v1_funct_1 @ X0)
% 1.20/1.39          | ~ (v1_funct_1 @ sk_C))),
% 1.20/1.39      inference('sup-', [status(thm)], ['133', '134'])).
% 1.20/1.39  thf('136', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('137', plain,
% 1.20/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.39         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.20/1.39            = (k5_relat_1 @ sk_C @ X0))
% 1.20/1.39          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.20/1.39          | ~ (v1_funct_1 @ X0))),
% 1.20/1.39      inference('demod', [status(thm)], ['135', '136'])).
% 1.20/1.39  thf('138', plain,
% 1.20/1.39      ((~ (v1_funct_1 @ sk_D)
% 1.20/1.39        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.20/1.39            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.20/1.39      inference('sup-', [status(thm)], ['132', '137'])).
% 1.20/1.39  thf('139', plain, ((v1_funct_1 @ sk_D)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('140', plain,
% 1.20/1.39      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.20/1.39        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.20/1.39        (k6_partfun1 @ sk_A))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('141', plain,
% 1.20/1.39      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('142', plain,
% 1.20/1.39      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf(dt_k1_partfun1, axiom,
% 1.20/1.39    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.20/1.39     ( ( ( v1_funct_1 @ E ) & 
% 1.20/1.39         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.20/1.39         ( v1_funct_1 @ F ) & 
% 1.20/1.39         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.20/1.39       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.20/1.39         ( m1_subset_1 @
% 1.20/1.39           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.20/1.39           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.20/1.39  thf('143', plain,
% 1.20/1.39      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.20/1.39         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 1.20/1.39          | ~ (v1_funct_1 @ X34)
% 1.20/1.39          | ~ (v1_funct_1 @ X37)
% 1.20/1.39          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.20/1.39          | (m1_subset_1 @ (k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37) @ 
% 1.20/1.39             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X39))))),
% 1.20/1.39      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.20/1.39  thf('144', plain,
% 1.20/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.39         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.20/1.39           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.20/1.39          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.20/1.39          | ~ (v1_funct_1 @ X1)
% 1.20/1.39          | ~ (v1_funct_1 @ sk_C))),
% 1.20/1.39      inference('sup-', [status(thm)], ['142', '143'])).
% 1.20/1.39  thf('145', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('146', plain,
% 1.20/1.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.39         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.20/1.39           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.20/1.39          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.20/1.39          | ~ (v1_funct_1 @ X1))),
% 1.20/1.39      inference('demod', [status(thm)], ['144', '145'])).
% 1.20/1.39  thf('147', plain,
% 1.20/1.39      ((~ (v1_funct_1 @ sk_D)
% 1.20/1.39        | (m1_subset_1 @ 
% 1.20/1.39           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.20/1.39           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.20/1.39      inference('sup-', [status(thm)], ['141', '146'])).
% 1.20/1.39  thf('148', plain, ((v1_funct_1 @ sk_D)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('149', plain,
% 1.20/1.39      ((m1_subset_1 @ 
% 1.20/1.39        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.20/1.39        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.20/1.39      inference('demod', [status(thm)], ['147', '148'])).
% 1.20/1.39  thf(redefinition_r2_relset_1, axiom,
% 1.20/1.39    (![A:$i,B:$i,C:$i,D:$i]:
% 1.20/1.39     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.20/1.39         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.20/1.39       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.20/1.39  thf('150', plain,
% 1.20/1.39      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.20/1.39         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.20/1.39          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.20/1.39          | ((X30) = (X33))
% 1.20/1.39          | ~ (r2_relset_1 @ X31 @ X32 @ X30 @ X33))),
% 1.20/1.39      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.20/1.39  thf('151', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.20/1.39             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 1.20/1.39          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 1.20/1.39          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.20/1.39      inference('sup-', [status(thm)], ['149', '150'])).
% 1.20/1.39  thf('152', plain,
% 1.20/1.39      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.20/1.39           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.20/1.39        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.20/1.39            = (k6_partfun1 @ sk_A)))),
% 1.20/1.39      inference('sup-', [status(thm)], ['140', '151'])).
% 1.20/1.39  thf('153', plain,
% 1.20/1.39      (![X41 : $i]:
% 1.20/1.39         (m1_subset_1 @ (k6_partfun1 @ X41) @ 
% 1.20/1.39          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X41)))),
% 1.20/1.39      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.20/1.39  thf('154', plain,
% 1.20/1.39      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.20/1.39         = (k6_partfun1 @ sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['152', '153'])).
% 1.20/1.39  thf('155', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.20/1.39      inference('demod', [status(thm)], ['138', '139', '154'])).
% 1.20/1.39  thf('156', plain, (![X16 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X16)) = (X16))),
% 1.20/1.39      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.20/1.39  thf('157', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 1.20/1.39      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.20/1.39  thf('158', plain,
% 1.20/1.39      (![X16 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X16)) = (X16))),
% 1.20/1.39      inference('demod', [status(thm)], ['156', '157'])).
% 1.20/1.39  thf('159', plain, (((sk_A) = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))),
% 1.20/1.39      inference('demod', [status(thm)], ['131', '155', '158'])).
% 1.20/1.39  thf(t167_relat_1, axiom,
% 1.20/1.39    (![A:$i,B:$i]:
% 1.20/1.39     ( ( v1_relat_1 @ B ) =>
% 1.20/1.39       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 1.20/1.39  thf('160', plain,
% 1.20/1.39      (![X9 : $i, X10 : $i]:
% 1.20/1.39         ((r1_tarski @ (k10_relat_1 @ X9 @ X10) @ (k1_relat_1 @ X9))
% 1.20/1.39          | ~ (v1_relat_1 @ X9))),
% 1.20/1.39      inference('cnf', [status(esa)], [t167_relat_1])).
% 1.20/1.39  thf('161', plain,
% 1.20/1.39      (![X0 : $i, X2 : $i]:
% 1.20/1.39         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.20/1.39      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.20/1.39  thf('162', plain,
% 1.20/1.39      (![X0 : $i, X1 : $i]:
% 1.20/1.39         (~ (v1_relat_1 @ X0)
% 1.20/1.39          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ (k10_relat_1 @ X0 @ X1))
% 1.20/1.39          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ X1)))),
% 1.20/1.39      inference('sup-', [status(thm)], ['160', '161'])).
% 1.20/1.39  thf('163', plain,
% 1.20/1.39      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)
% 1.20/1.39        | ((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 1.20/1.39        | ~ (v1_relat_1 @ sk_C))),
% 1.20/1.39      inference('sup-', [status(thm)], ['159', '162'])).
% 1.20/1.39  thf('164', plain,
% 1.20/1.39      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('165', plain,
% 1.20/1.39      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.20/1.39         ((v4_relat_1 @ X24 @ X25)
% 1.20/1.39          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.20/1.39      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.20/1.39  thf('166', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 1.20/1.39      inference('sup-', [status(thm)], ['164', '165'])).
% 1.20/1.39  thf('167', plain,
% 1.20/1.39      (![X5 : $i, X6 : $i]:
% 1.20/1.39         (~ (v4_relat_1 @ X5 @ X6)
% 1.20/1.39          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 1.20/1.39          | ~ (v1_relat_1 @ X5))),
% 1.20/1.39      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.20/1.39  thf('168', plain,
% 1.20/1.39      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 1.20/1.39      inference('sup-', [status(thm)], ['166', '167'])).
% 1.20/1.39  thf('169', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.39      inference('demod', [status(thm)], ['29', '30'])).
% 1.20/1.39  thf('170', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 1.20/1.39      inference('demod', [status(thm)], ['168', '169'])).
% 1.20/1.39  thf('171', plain, (((sk_A) = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))),
% 1.20/1.39      inference('demod', [status(thm)], ['131', '155', '158'])).
% 1.20/1.39  thf('172', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.39      inference('demod', [status(thm)], ['29', '30'])).
% 1.20/1.39  thf('173', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['163', '170', '171', '172'])).
% 1.20/1.39  thf('174', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.20/1.39      inference('demod', [status(thm)], ['64', '65'])).
% 1.20/1.39  thf('175', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.39      inference('demod', [status(thm)], ['29', '30'])).
% 1.20/1.39  thf('176', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('177', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('178', plain,
% 1.20/1.39      (![X21 : $i]:
% 1.20/1.39         ((v1_relat_1 @ (k2_funct_1 @ X21))
% 1.20/1.39          | ~ (v1_funct_1 @ X21)
% 1.20/1.39          | ~ (v1_relat_1 @ X21))),
% 1.20/1.39      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.20/1.39  thf('179', plain,
% 1.20/1.39      (![X23 : $i]:
% 1.20/1.39         (~ (v2_funct_1 @ X23)
% 1.20/1.39          | ((k5_relat_1 @ X23 @ (k2_funct_1 @ X23))
% 1.20/1.39              = (k6_partfun1 @ (k1_relat_1 @ X23)))
% 1.20/1.39          | ~ (v1_funct_1 @ X23)
% 1.20/1.39          | ~ (v1_relat_1 @ X23))),
% 1.20/1.39      inference('demod', [status(thm)], ['1', '2'])).
% 1.20/1.39  thf('180', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 1.20/1.39      inference('demod', [status(thm)], ['168', '169'])).
% 1.20/1.39  thf('181', plain,
% 1.20/1.39      (![X18 : $i, X19 : $i]:
% 1.20/1.39         (~ (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 1.20/1.39          | ((k5_relat_1 @ (k6_partfun1 @ X19) @ X18) = (X18))
% 1.20/1.39          | ~ (v1_relat_1 @ X18))),
% 1.20/1.39      inference('demod', [status(thm)], ['51', '52'])).
% 1.20/1.39  thf('182', plain,
% 1.20/1.39      ((~ (v1_relat_1 @ sk_C)
% 1.20/1.39        | ((k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C) = (sk_C)))),
% 1.20/1.39      inference('sup-', [status(thm)], ['180', '181'])).
% 1.20/1.39  thf('183', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.39      inference('demod', [status(thm)], ['29', '30'])).
% 1.20/1.39  thf('184', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C) = (sk_C))),
% 1.20/1.39      inference('demod', [status(thm)], ['182', '183'])).
% 1.20/1.39  thf('185', plain,
% 1.20/1.39      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.20/1.39         (~ (v1_relat_1 @ X13)
% 1.20/1.39          | ((k5_relat_1 @ (k5_relat_1 @ X14 @ X13) @ X15)
% 1.20/1.39              = (k5_relat_1 @ X14 @ (k5_relat_1 @ X13 @ X15)))
% 1.20/1.39          | ~ (v1_relat_1 @ X15)
% 1.20/1.39          | ~ (v1_relat_1 @ X14))),
% 1.20/1.39      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.20/1.39  thf('186', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (((k5_relat_1 @ sk_C @ X0)
% 1.20/1.39            = (k5_relat_1 @ (k6_partfun1 @ sk_A) @ (k5_relat_1 @ sk_C @ X0)))
% 1.20/1.39          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_A))
% 1.20/1.39          | ~ (v1_relat_1 @ X0)
% 1.20/1.39          | ~ (v1_relat_1 @ sk_C))),
% 1.20/1.39      inference('sup+', [status(thm)], ['184', '185'])).
% 1.20/1.39  thf('187', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.20/1.39      inference('demod', [status(thm)], ['64', '65'])).
% 1.20/1.39  thf('188', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.39      inference('demod', [status(thm)], ['29', '30'])).
% 1.20/1.39  thf('189', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (((k5_relat_1 @ sk_C @ X0)
% 1.20/1.39            = (k5_relat_1 @ (k6_partfun1 @ sk_A) @ (k5_relat_1 @ sk_C @ X0)))
% 1.20/1.39          | ~ (v1_relat_1 @ X0))),
% 1.20/1.39      inference('demod', [status(thm)], ['186', '187', '188'])).
% 1.20/1.39  thf('190', plain,
% 1.20/1.39      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.20/1.39          = (k5_relat_1 @ (k6_partfun1 @ sk_A) @ 
% 1.20/1.39             (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 1.20/1.39        | ~ (v1_relat_1 @ sk_C)
% 1.20/1.39        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.39        | ~ (v2_funct_1 @ sk_C)
% 1.20/1.39        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.39      inference('sup+', [status(thm)], ['179', '189'])).
% 1.20/1.39  thf('191', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 1.20/1.39      inference('demod', [status(thm)], ['168', '169'])).
% 1.20/1.39  thf('192', plain,
% 1.20/1.39      (![X16 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X16)) = (X16))),
% 1.20/1.39      inference('demod', [status(thm)], ['156', '157'])).
% 1.20/1.39  thf('193', plain,
% 1.20/1.39      (![X18 : $i, X19 : $i]:
% 1.20/1.39         (~ (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 1.20/1.39          | ((k5_relat_1 @ (k6_partfun1 @ X19) @ X18) = (X18))
% 1.20/1.39          | ~ (v1_relat_1 @ X18))),
% 1.20/1.39      inference('demod', [status(thm)], ['51', '52'])).
% 1.20/1.39  thf('194', plain,
% 1.20/1.39      (![X0 : $i, X1 : $i]:
% 1.20/1.39         (~ (r1_tarski @ X0 @ X1)
% 1.20/1.39          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.20/1.39          | ((k5_relat_1 @ (k6_partfun1 @ X1) @ (k6_partfun1 @ X0))
% 1.20/1.39              = (k6_partfun1 @ X0)))),
% 1.20/1.39      inference('sup-', [status(thm)], ['192', '193'])).
% 1.20/1.39  thf('195', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.20/1.39      inference('demod', [status(thm)], ['64', '65'])).
% 1.20/1.39  thf('196', plain,
% 1.20/1.39      (![X0 : $i, X1 : $i]:
% 1.20/1.39         (~ (r1_tarski @ X0 @ X1)
% 1.20/1.39          | ((k5_relat_1 @ (k6_partfun1 @ X1) @ (k6_partfun1 @ X0))
% 1.20/1.39              = (k6_partfun1 @ X0)))),
% 1.20/1.39      inference('demod', [status(thm)], ['194', '195'])).
% 1.20/1.39  thf('197', plain,
% 1.20/1.39      (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ 
% 1.20/1.39         (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 1.20/1.39         = (k6_partfun1 @ (k1_relat_1 @ sk_C)))),
% 1.20/1.39      inference('sup-', [status(thm)], ['191', '196'])).
% 1.20/1.39  thf('198', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.39      inference('demod', [status(thm)], ['29', '30'])).
% 1.20/1.39  thf('199', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('200', plain, ((v2_funct_1 @ sk_C)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('201', plain,
% 1.20/1.39      ((((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.20/1.39          = (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 1.20/1.39        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.20/1.39      inference('demod', [status(thm)], ['190', '197', '198', '199', '200'])).
% 1.20/1.39  thf('202', plain,
% 1.20/1.39      ((~ (v1_relat_1 @ sk_C)
% 1.20/1.39        | ~ (v1_funct_1 @ sk_C)
% 1.20/1.39        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.20/1.39            = (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 1.20/1.39      inference('sup-', [status(thm)], ['178', '201'])).
% 1.20/1.39  thf('203', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.39      inference('demod', [status(thm)], ['29', '30'])).
% 1.20/1.39  thf('204', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('205', plain,
% 1.20/1.39      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 1.20/1.39         = (k6_partfun1 @ (k1_relat_1 @ sk_C)))),
% 1.20/1.39      inference('demod', [status(thm)], ['202', '203', '204'])).
% 1.20/1.39  thf('206', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['163', '170', '171', '172'])).
% 1.20/1.39  thf('207', plain,
% 1.20/1.39      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 1.20/1.39      inference('demod', [status(thm)], ['205', '206'])).
% 1.20/1.39  thf('208', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 1.20/1.39      inference('demod', [status(thm)], ['138', '139', '154'])).
% 1.20/1.39  thf('209', plain,
% 1.20/1.39      (![X0 : $i]:
% 1.20/1.39         (~ (v1_relat_1 @ X0)
% 1.20/1.39          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.20/1.39              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.20/1.39      inference('demod', [status(thm)], ['92', '93', '94'])).
% 1.20/1.39  thf('210', plain,
% 1.20/1.39      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.20/1.39          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 1.20/1.39        | ~ (v1_relat_1 @ sk_D))),
% 1.20/1.39      inference('sup+', [status(thm)], ['208', '209'])).
% 1.20/1.39  thf('211', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 1.20/1.39      inference('demod', [status(thm)], ['111', '112'])).
% 1.20/1.39  thf('212', plain, ((v1_relat_1 @ sk_D)),
% 1.20/1.39      inference('demod', [status(thm)], ['106', '107'])).
% 1.20/1.39  thf('213', plain,
% 1.20/1.39      (((sk_D) = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))),
% 1.20/1.39      inference('demod', [status(thm)], ['210', '211', '212'])).
% 1.20/1.39  thf('214', plain,
% 1.20/1.39      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.20/1.39         = (k2_funct_1 @ sk_C))),
% 1.20/1.39      inference('demod', [status(thm)], ['56', '57', '58'])).
% 1.20/1.39  thf('215', plain,
% 1.20/1.39      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.20/1.39         = (k2_funct_1 @ sk_C))),
% 1.20/1.39      inference('demod', [status(thm)], ['56', '57', '58'])).
% 1.20/1.39  thf('216', plain,
% 1.20/1.39      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C)) | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 1.20/1.39      inference('demod', [status(thm)],
% 1.20/1.39                ['98', '173', '174', '175', '176', '177', '207', '213', '214', 
% 1.20/1.39                 '215'])).
% 1.20/1.39  thf('217', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('218', plain, (~ (v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.20/1.39      inference('simplify_reflect-', [status(thm)], ['216', '217'])).
% 1.20/1.39  thf('219', plain, ((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C))),
% 1.20/1.39      inference('sup-', [status(thm)], ['0', '218'])).
% 1.20/1.39  thf('220', plain, ((v1_relat_1 @ sk_C)),
% 1.20/1.39      inference('demod', [status(thm)], ['29', '30'])).
% 1.20/1.39  thf('221', plain, ((v1_funct_1 @ sk_C)),
% 1.20/1.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.39  thf('222', plain, ($false),
% 1.20/1.39      inference('demod', [status(thm)], ['219', '220', '221'])).
% 1.20/1.39  
% 1.20/1.39  % SZS output end Refutation
% 1.20/1.39  
% 1.20/1.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
