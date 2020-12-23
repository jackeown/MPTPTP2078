%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yyujIttN3c

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:17 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  258 ( 703 expanded)
%              Number of leaves         :   49 ( 236 expanded)
%              Depth                    :   38
%              Number of atoms          : 2002 (12225 expanded)
%              Number of equality atoms :  121 ( 804 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['4','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('13',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('16',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X21 @ ( k2_relat_1 @ X22 ) )
      | ( ( k9_relat_1 @ X22 @ ( k10_relat_1 @ X22 @ X21 ) )
        = X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('22',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['17','22','23'])).

thf('25',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','24'])).

thf('26',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( ( k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45 )
        = ( k5_relat_1 @ X42 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['26','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
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

thf('39',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('46',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('47',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( X31 = X34 )
      | ~ ( r2_relset_1 @ X32 @ X33 @ X31 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','48'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('50',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('51',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('52',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['49','52'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('54',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) )
        = ( k10_relat_1 @ X9 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('55',plain,
    ( ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
      = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('56',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('57',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('58',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X15 ) )
      = X15 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('60',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('61',plain,
    ( sk_A
    = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['55','58','59','60'])).

thf('62',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['25','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('65',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['63','64'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('66',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k7_relat_1 @ X10 @ X11 ) )
      | ~ ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('67',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('69',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('70',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) )
        = ( k9_relat_1 @ X6 @ X7 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('71',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('73',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['13','14'])).

thf('75',plain,
    ( sk_B
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['62','75'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('77',plain,(
    ! [X17: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X17 ) ) @ X17 )
        = X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('78',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('79',plain,(
    ! [X17: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X17 ) ) @ X17 )
        = X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['76','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('82',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['49','52'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('84',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
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

thf('85',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X24 ) @ X24 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('86',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('87',plain,(
    ! [X24: $i] :
      ( ~ ( v2_funct_1 @ X24 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X24 ) @ X24 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('89',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
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

thf('90',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k2_relat_1 @ X23 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('91',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('92',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['13','14'])).

thf('93',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('94',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k2_relat_1 @ X23 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('95',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('96',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X15 ) )
      = X15 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('106',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['99','104','105'])).

thf('107',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ( v4_relat_1 @ X2 @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['94','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['93','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['92','111'])).

thf('113',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('114',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['112','113','114','115'])).

thf('117',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('118',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['91','118'])).

thf('120',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('121',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X15 ) )
      = X15 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('124',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ( v4_relat_1 @ X2 @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    v4_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ sk_B ),
    inference('sup-',[status(thm)],['122','127'])).

thf('129',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k7_relat_1 @ X10 @ X11 ) )
      | ~ ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('130',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k7_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('132',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    = ( k7_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k7_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['90','132'])).

thf('134',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['13','14'])).

thf('135',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('136',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k7_relat_1 @ X10 @ X11 ) )
      | ~ ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k6_partfun1 @ X0 )
        = ( k7_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k6_partfun1 @ X0 )
      = ( k7_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('141',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['133','134','139','140','141','142'])).

thf('144',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X15 ) )
      = X15 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('145',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X15 ) )
      = X15 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('147',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X17: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X17 ) ) @ X17 )
        = X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('149',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['89','149'])).

thf('151',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('152',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['150','151','152'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('154',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) @ X14 )
        = ( k5_relat_1 @ X13 @ ( k5_relat_1 @ X12 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['88','157'])).

thf('159',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('160',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('162',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['87','161'])).

thf('163',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['13','14'])).

thf('164',plain,(
    ! [X15: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X15 ) )
      = X15 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('165',plain,(
    ! [X17: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X17 ) ) @ X17 )
        = X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('170',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('173',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['162','163','168','169','170','171','172'])).

thf('174',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) @ X14 )
        = ( k5_relat_1 @ X13 @ ( k5_relat_1 @ X12 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['173','174'])).

thf('176',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['84','177'])).

thf('179',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('180',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['178','179','180'])).

thf('182',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['83','181'])).

thf('183',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('184',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['63','64'])).

thf('185',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('186',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('188',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k1_relat_1 @ X23 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('190',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ( ( k5_relat_1 @ X18 @ ( k6_relat_1 @ X19 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('191',plain,(
    ! [X48: $i] :
      ( ( k6_partfun1 @ X48 )
      = ( k6_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('192',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ( ( k5_relat_1 @ X18 @ ( k6_partfun1 @ X19 ) )
        = X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ X1 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['189','192'])).

thf('194',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['188','193'])).

thf('195',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('198',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['194','195','196','197'])).

thf('199',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['183','198'])).

thf('200',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('201',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['199','200','201'])).

thf('203',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['7','8'])).

thf('204',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['182','202','203'])).

thf('205',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['82','204'])).

thf('206',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['205','206'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yyujIttN3c
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:19:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.52/0.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.75  % Solved by: fo/fo7.sh
% 0.52/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.75  % done 483 iterations in 0.288s
% 0.52/0.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.75  % SZS output start Refutation
% 0.52/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.75  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.52/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.52/0.75  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.52/0.75  thf(sk_D_type, type, sk_D: $i).
% 0.52/0.75  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.52/0.75  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.52/0.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.75  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.52/0.75  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.52/0.75  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.52/0.75  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.52/0.75  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.52/0.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.52/0.75  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.52/0.75  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.52/0.75  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.52/0.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.75  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.52/0.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.75  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.52/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.75  thf(sk_C_type, type, sk_C: $i).
% 0.52/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.75  thf(t36_funct_2, conjecture,
% 0.52/0.75    (![A:$i,B:$i,C:$i]:
% 0.52/0.75     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.52/0.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.75       ( ![D:$i]:
% 0.52/0.75         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.52/0.75             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.52/0.75           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.52/0.75               ( r2_relset_1 @
% 0.52/0.75                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.52/0.75                 ( k6_partfun1 @ A ) ) & 
% 0.52/0.75               ( v2_funct_1 @ C ) ) =>
% 0.52/0.75             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.52/0.75               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.52/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.75    (~( ![A:$i,B:$i,C:$i]:
% 0.52/0.75        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.52/0.75            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.75          ( ![D:$i]:
% 0.52/0.75            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.52/0.75                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.52/0.75              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.52/0.75                  ( r2_relset_1 @
% 0.52/0.75                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.52/0.75                    ( k6_partfun1 @ A ) ) & 
% 0.52/0.75                  ( v2_funct_1 @ C ) ) =>
% 0.52/0.75                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.52/0.75                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.52/0.75    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.52/0.75  thf('0', plain,
% 0.52/0.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf(cc2_relset_1, axiom,
% 0.52/0.75    (![A:$i,B:$i,C:$i]:
% 0.52/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.75       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.52/0.75  thf('1', plain,
% 0.52/0.75      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.52/0.75         ((v4_relat_1 @ X25 @ X26)
% 0.52/0.75          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.52/0.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.52/0.75  thf('2', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 0.52/0.75      inference('sup-', [status(thm)], ['0', '1'])).
% 0.52/0.75  thf(d18_relat_1, axiom,
% 0.52/0.75    (![A:$i,B:$i]:
% 0.52/0.75     ( ( v1_relat_1 @ B ) =>
% 0.52/0.75       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.52/0.75  thf('3', plain,
% 0.52/0.75      (![X2 : $i, X3 : $i]:
% 0.52/0.75         (~ (v4_relat_1 @ X2 @ X3)
% 0.52/0.75          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 0.52/0.75          | ~ (v1_relat_1 @ X2))),
% 0.52/0.75      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.52/0.75  thf('4', plain,
% 0.52/0.75      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 0.52/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.75  thf('5', plain,
% 0.52/0.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf(cc2_relat_1, axiom,
% 0.52/0.75    (![A:$i]:
% 0.52/0.75     ( ( v1_relat_1 @ A ) =>
% 0.52/0.75       ( ![B:$i]:
% 0.52/0.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.52/0.75  thf('6', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.52/0.75          | (v1_relat_1 @ X0)
% 0.52/0.75          | ~ (v1_relat_1 @ X1))),
% 0.52/0.75      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.52/0.75  thf('7', plain,
% 0.52/0.75      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.52/0.75      inference('sup-', [status(thm)], ['5', '6'])).
% 0.52/0.75  thf(fc6_relat_1, axiom,
% 0.52/0.75    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.52/0.75  thf('8', plain,
% 0.52/0.75      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.52/0.75      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.52/0.75  thf('9', plain, ((v1_relat_1 @ sk_D)),
% 0.52/0.75      inference('demod', [status(thm)], ['7', '8'])).
% 0.52/0.75  thf('10', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 0.52/0.75      inference('demod', [status(thm)], ['4', '9'])).
% 0.52/0.75  thf('11', plain,
% 0.52/0.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf(redefinition_k2_relset_1, axiom,
% 0.52/0.75    (![A:$i,B:$i,C:$i]:
% 0.52/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.75       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.52/0.75  thf('12', plain,
% 0.52/0.75      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.52/0.75         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 0.52/0.75          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.52/0.75      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.52/0.75  thf('13', plain,
% 0.52/0.75      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.52/0.75      inference('sup-', [status(thm)], ['11', '12'])).
% 0.52/0.75  thf('14', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('15', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.52/0.75      inference('sup+', [status(thm)], ['13', '14'])).
% 0.52/0.75  thf(t147_funct_1, axiom,
% 0.52/0.75    (![A:$i,B:$i]:
% 0.52/0.75     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.52/0.75       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.52/0.75         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.52/0.75  thf('16', plain,
% 0.52/0.75      (![X21 : $i, X22 : $i]:
% 0.52/0.75         (~ (r1_tarski @ X21 @ (k2_relat_1 @ X22))
% 0.52/0.75          | ((k9_relat_1 @ X22 @ (k10_relat_1 @ X22 @ X21)) = (X21))
% 0.52/0.75          | ~ (v1_funct_1 @ X22)
% 0.52/0.75          | ~ (v1_relat_1 @ X22))),
% 0.52/0.75      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.52/0.75  thf('17', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         (~ (r1_tarski @ X0 @ sk_B)
% 0.52/0.75          | ~ (v1_relat_1 @ sk_C)
% 0.52/0.75          | ~ (v1_funct_1 @ sk_C)
% 0.52/0.75          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['15', '16'])).
% 0.52/0.75  thf('18', plain,
% 0.52/0.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('19', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.52/0.75          | (v1_relat_1 @ X0)
% 0.52/0.75          | ~ (v1_relat_1 @ X1))),
% 0.52/0.75      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.52/0.75  thf('20', plain,
% 0.52/0.75      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.52/0.75      inference('sup-', [status(thm)], ['18', '19'])).
% 0.52/0.75  thf('21', plain,
% 0.52/0.75      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.52/0.75      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.52/0.75  thf('22', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.75      inference('demod', [status(thm)], ['20', '21'])).
% 0.52/0.75  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('24', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         (~ (r1_tarski @ X0 @ sk_B)
% 0.52/0.75          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 0.52/0.75      inference('demod', [status(thm)], ['17', '22', '23'])).
% 0.52/0.75  thf('25', plain,
% 0.52/0.75      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 0.52/0.75         = (k1_relat_1 @ sk_D))),
% 0.52/0.75      inference('sup-', [status(thm)], ['10', '24'])).
% 0.52/0.75  thf('26', plain,
% 0.52/0.75      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.52/0.75        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.52/0.75        (k6_partfun1 @ sk_A))),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('27', plain,
% 0.52/0.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('28', plain,
% 0.52/0.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf(redefinition_k1_partfun1, axiom,
% 0.52/0.75    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.52/0.75     ( ( ( v1_funct_1 @ E ) & 
% 0.52/0.75         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.52/0.75         ( v1_funct_1 @ F ) & 
% 0.52/0.75         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.52/0.75       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.52/0.75  thf('29', plain,
% 0.52/0.75      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.52/0.75         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.52/0.75          | ~ (v1_funct_1 @ X42)
% 0.52/0.75          | ~ (v1_funct_1 @ X45)
% 0.52/0.75          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 0.52/0.75          | ((k1_partfun1 @ X43 @ X44 @ X46 @ X47 @ X42 @ X45)
% 0.52/0.75              = (k5_relat_1 @ X42 @ X45)))),
% 0.52/0.75      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.52/0.75  thf('30', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.75         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.52/0.75            = (k5_relat_1 @ sk_C @ X0))
% 0.52/0.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.52/0.75          | ~ (v1_funct_1 @ X0)
% 0.52/0.75          | ~ (v1_funct_1 @ sk_C))),
% 0.52/0.75      inference('sup-', [status(thm)], ['28', '29'])).
% 0.52/0.75  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('32', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.75         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.52/0.75            = (k5_relat_1 @ sk_C @ X0))
% 0.52/0.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.52/0.75          | ~ (v1_funct_1 @ X0))),
% 0.52/0.75      inference('demod', [status(thm)], ['30', '31'])).
% 0.52/0.75  thf('33', plain,
% 0.52/0.75      ((~ (v1_funct_1 @ sk_D)
% 0.52/0.75        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.52/0.75            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['27', '32'])).
% 0.52/0.75  thf('34', plain, ((v1_funct_1 @ sk_D)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('35', plain,
% 0.52/0.75      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.52/0.75         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.52/0.75      inference('demod', [status(thm)], ['33', '34'])).
% 0.52/0.75  thf('36', plain,
% 0.52/0.75      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.52/0.75        (k6_partfun1 @ sk_A))),
% 0.52/0.75      inference('demod', [status(thm)], ['26', '35'])).
% 0.52/0.75  thf('37', plain,
% 0.52/0.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('38', plain,
% 0.52/0.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf(dt_k1_partfun1, axiom,
% 0.52/0.75    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.52/0.75     ( ( ( v1_funct_1 @ E ) & 
% 0.52/0.75         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.52/0.75         ( v1_funct_1 @ F ) & 
% 0.52/0.75         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.52/0.75       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.52/0.75         ( m1_subset_1 @
% 0.52/0.75           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.52/0.75           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.52/0.75  thf('39', plain,
% 0.52/0.75      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.52/0.75         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.52/0.75          | ~ (v1_funct_1 @ X36)
% 0.52/0.75          | ~ (v1_funct_1 @ X39)
% 0.52/0.75          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.52/0.75          | (m1_subset_1 @ (k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39) @ 
% 0.52/0.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X41))))),
% 0.52/0.75      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.52/0.75  thf('40', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.75         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.52/0.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.52/0.75          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.52/0.75          | ~ (v1_funct_1 @ X1)
% 0.52/0.75          | ~ (v1_funct_1 @ sk_C))),
% 0.52/0.75      inference('sup-', [status(thm)], ['38', '39'])).
% 0.52/0.75  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('42', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.75         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.52/0.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.52/0.75          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.52/0.75          | ~ (v1_funct_1 @ X1))),
% 0.52/0.75      inference('demod', [status(thm)], ['40', '41'])).
% 0.52/0.75  thf('43', plain,
% 0.52/0.75      ((~ (v1_funct_1 @ sk_D)
% 0.52/0.75        | (m1_subset_1 @ 
% 0.52/0.75           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.52/0.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.52/0.75      inference('sup-', [status(thm)], ['37', '42'])).
% 0.52/0.75  thf('44', plain, ((v1_funct_1 @ sk_D)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('45', plain,
% 0.52/0.75      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.52/0.75         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.52/0.75      inference('demod', [status(thm)], ['33', '34'])).
% 0.52/0.75  thf('46', plain,
% 0.52/0.75      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.52/0.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.52/0.75      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.52/0.75  thf(redefinition_r2_relset_1, axiom,
% 0.52/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.75     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.52/0.75         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.75       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.52/0.75  thf('47', plain,
% 0.52/0.75      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.52/0.75         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.52/0.75          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.52/0.75          | ((X31) = (X34))
% 0.52/0.75          | ~ (r2_relset_1 @ X32 @ X33 @ X31 @ X34))),
% 0.52/0.75      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.52/0.75  thf('48', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.52/0.75          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.52/0.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.52/0.75      inference('sup-', [status(thm)], ['46', '47'])).
% 0.52/0.75  thf('49', plain,
% 0.52/0.75      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.52/0.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.52/0.75        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['36', '48'])).
% 0.52/0.75  thf(t29_relset_1, axiom,
% 0.52/0.75    (![A:$i]:
% 0.52/0.75     ( m1_subset_1 @
% 0.52/0.75       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.52/0.75  thf('50', plain,
% 0.52/0.75      (![X35 : $i]:
% 0.52/0.75         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 0.52/0.75          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.52/0.75      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.52/0.75  thf(redefinition_k6_partfun1, axiom,
% 0.52/0.75    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.52/0.75  thf('51', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 0.52/0.75      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.52/0.75  thf('52', plain,
% 0.52/0.75      (![X35 : $i]:
% 0.52/0.75         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 0.52/0.75          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.52/0.75      inference('demod', [status(thm)], ['50', '51'])).
% 0.52/0.75  thf('53', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.52/0.75      inference('demod', [status(thm)], ['49', '52'])).
% 0.52/0.75  thf(t182_relat_1, axiom,
% 0.52/0.75    (![A:$i]:
% 0.52/0.75     ( ( v1_relat_1 @ A ) =>
% 0.52/0.75       ( ![B:$i]:
% 0.52/0.75         ( ( v1_relat_1 @ B ) =>
% 0.52/0.75           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.52/0.75             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.52/0.75  thf('54', plain,
% 0.52/0.75      (![X8 : $i, X9 : $i]:
% 0.52/0.75         (~ (v1_relat_1 @ X8)
% 0.52/0.75          | ((k1_relat_1 @ (k5_relat_1 @ X9 @ X8))
% 0.52/0.75              = (k10_relat_1 @ X9 @ (k1_relat_1 @ X8)))
% 0.52/0.75          | ~ (v1_relat_1 @ X9))),
% 0.52/0.75      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.52/0.75  thf('55', plain,
% 0.52/0.75      ((((k1_relat_1 @ (k6_partfun1 @ sk_A))
% 0.52/0.75          = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 0.52/0.75        | ~ (v1_relat_1 @ sk_C)
% 0.52/0.75        | ~ (v1_relat_1 @ sk_D))),
% 0.52/0.75      inference('sup+', [status(thm)], ['53', '54'])).
% 0.52/0.75  thf(t71_relat_1, axiom,
% 0.52/0.75    (![A:$i]:
% 0.52/0.75     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.52/0.75       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.52/0.75  thf('56', plain, (![X15 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X15)) = (X15))),
% 0.52/0.75      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.52/0.75  thf('57', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 0.52/0.75      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.52/0.75  thf('58', plain, (![X15 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X15)) = (X15))),
% 0.52/0.75      inference('demod', [status(thm)], ['56', '57'])).
% 0.52/0.75  thf('59', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.75      inference('demod', [status(thm)], ['20', '21'])).
% 0.52/0.75  thf('60', plain, ((v1_relat_1 @ sk_D)),
% 0.52/0.75      inference('demod', [status(thm)], ['7', '8'])).
% 0.52/0.75  thf('61', plain, (((sk_A) = (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))),
% 0.52/0.75      inference('demod', [status(thm)], ['55', '58', '59', '60'])).
% 0.52/0.75  thf('62', plain, (((k9_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.52/0.75      inference('demod', [status(thm)], ['25', '61'])).
% 0.52/0.75  thf('63', plain,
% 0.52/0.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('64', plain,
% 0.52/0.75      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.52/0.75         ((v4_relat_1 @ X25 @ X26)
% 0.52/0.75          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.52/0.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.52/0.75  thf('65', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.52/0.75      inference('sup-', [status(thm)], ['63', '64'])).
% 0.52/0.75  thf(t209_relat_1, axiom,
% 0.52/0.75    (![A:$i,B:$i]:
% 0.52/0.75     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.52/0.75       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.52/0.75  thf('66', plain,
% 0.52/0.75      (![X10 : $i, X11 : $i]:
% 0.52/0.75         (((X10) = (k7_relat_1 @ X10 @ X11))
% 0.52/0.75          | ~ (v4_relat_1 @ X10 @ X11)
% 0.52/0.75          | ~ (v1_relat_1 @ X10))),
% 0.52/0.75      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.52/0.75  thf('67', plain,
% 0.52/0.75      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['65', '66'])).
% 0.52/0.75  thf('68', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.75      inference('demod', [status(thm)], ['20', '21'])).
% 0.52/0.75  thf('69', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.52/0.75      inference('demod', [status(thm)], ['67', '68'])).
% 0.52/0.75  thf(t148_relat_1, axiom,
% 0.52/0.75    (![A:$i,B:$i]:
% 0.52/0.75     ( ( v1_relat_1 @ B ) =>
% 0.52/0.75       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.52/0.75  thf('70', plain,
% 0.52/0.75      (![X6 : $i, X7 : $i]:
% 0.52/0.75         (((k2_relat_1 @ (k7_relat_1 @ X6 @ X7)) = (k9_relat_1 @ X6 @ X7))
% 0.52/0.75          | ~ (v1_relat_1 @ X6))),
% 0.52/0.75      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.52/0.75  thf('71', plain,
% 0.52/0.75      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 0.52/0.75        | ~ (v1_relat_1 @ sk_C))),
% 0.52/0.75      inference('sup+', [status(thm)], ['69', '70'])).
% 0.52/0.75  thf('72', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.75      inference('demod', [status(thm)], ['20', '21'])).
% 0.52/0.75  thf('73', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.52/0.75      inference('demod', [status(thm)], ['71', '72'])).
% 0.52/0.75  thf('74', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.52/0.75      inference('sup+', [status(thm)], ['13', '14'])).
% 0.52/0.75  thf('75', plain, (((sk_B) = (k9_relat_1 @ sk_C @ sk_A))),
% 0.52/0.75      inference('demod', [status(thm)], ['73', '74'])).
% 0.52/0.75  thf('76', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.52/0.75      inference('sup+', [status(thm)], ['62', '75'])).
% 0.52/0.75  thf(t78_relat_1, axiom,
% 0.52/0.75    (![A:$i]:
% 0.52/0.75     ( ( v1_relat_1 @ A ) =>
% 0.52/0.75       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 0.52/0.75  thf('77', plain,
% 0.52/0.75      (![X17 : $i]:
% 0.52/0.75         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X17)) @ X17) = (X17))
% 0.52/0.75          | ~ (v1_relat_1 @ X17))),
% 0.52/0.75      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.52/0.75  thf('78', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 0.52/0.75      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.52/0.75  thf('79', plain,
% 0.52/0.75      (![X17 : $i]:
% 0.52/0.75         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X17)) @ X17) = (X17))
% 0.52/0.75          | ~ (v1_relat_1 @ X17))),
% 0.52/0.75      inference('demod', [status(thm)], ['77', '78'])).
% 0.52/0.75  thf('80', plain,
% 0.52/0.75      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))
% 0.52/0.75        | ~ (v1_relat_1 @ sk_D))),
% 0.52/0.75      inference('sup+', [status(thm)], ['76', '79'])).
% 0.52/0.75  thf('81', plain, ((v1_relat_1 @ sk_D)),
% 0.52/0.75      inference('demod', [status(thm)], ['7', '8'])).
% 0.52/0.75  thf('82', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 0.52/0.75      inference('demod', [status(thm)], ['80', '81'])).
% 0.52/0.75  thf('83', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.52/0.75      inference('demod', [status(thm)], ['49', '52'])).
% 0.52/0.75  thf(dt_k2_funct_1, axiom,
% 0.52/0.75    (![A:$i]:
% 0.52/0.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.52/0.75       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.52/0.75         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.52/0.75  thf('84', plain,
% 0.52/0.75      (![X20 : $i]:
% 0.52/0.75         ((v1_relat_1 @ (k2_funct_1 @ X20))
% 0.52/0.75          | ~ (v1_funct_1 @ X20)
% 0.52/0.75          | ~ (v1_relat_1 @ X20))),
% 0.52/0.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.52/0.75  thf(t61_funct_1, axiom,
% 0.52/0.75    (![A:$i]:
% 0.52/0.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.52/0.75       ( ( v2_funct_1 @ A ) =>
% 0.52/0.75         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.52/0.75             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.52/0.75           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.52/0.75             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.52/0.75  thf('85', plain,
% 0.52/0.75      (![X24 : $i]:
% 0.52/0.75         (~ (v2_funct_1 @ X24)
% 0.52/0.75          | ((k5_relat_1 @ (k2_funct_1 @ X24) @ X24)
% 0.52/0.75              = (k6_relat_1 @ (k2_relat_1 @ X24)))
% 0.52/0.75          | ~ (v1_funct_1 @ X24)
% 0.52/0.75          | ~ (v1_relat_1 @ X24))),
% 0.52/0.75      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.52/0.75  thf('86', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 0.52/0.75      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.52/0.75  thf('87', plain,
% 0.52/0.75      (![X24 : $i]:
% 0.52/0.75         (~ (v2_funct_1 @ X24)
% 0.52/0.75          | ((k5_relat_1 @ (k2_funct_1 @ X24) @ X24)
% 0.52/0.75              = (k6_partfun1 @ (k2_relat_1 @ X24)))
% 0.52/0.75          | ~ (v1_funct_1 @ X24)
% 0.52/0.75          | ~ (v1_relat_1 @ X24))),
% 0.52/0.75      inference('demod', [status(thm)], ['85', '86'])).
% 0.52/0.75  thf('88', plain,
% 0.52/0.75      (![X20 : $i]:
% 0.52/0.75         ((v1_relat_1 @ (k2_funct_1 @ X20))
% 0.52/0.75          | ~ (v1_funct_1 @ X20)
% 0.52/0.75          | ~ (v1_relat_1 @ X20))),
% 0.52/0.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.52/0.75  thf('89', plain,
% 0.52/0.75      (![X20 : $i]:
% 0.52/0.75         ((v1_relat_1 @ (k2_funct_1 @ X20))
% 0.52/0.75          | ~ (v1_funct_1 @ X20)
% 0.52/0.75          | ~ (v1_relat_1 @ X20))),
% 0.52/0.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.52/0.75  thf(t55_funct_1, axiom,
% 0.52/0.75    (![A:$i]:
% 0.52/0.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.52/0.75       ( ( v2_funct_1 @ A ) =>
% 0.52/0.75         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.52/0.75           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.52/0.75  thf('90', plain,
% 0.52/0.75      (![X23 : $i]:
% 0.52/0.75         (~ (v2_funct_1 @ X23)
% 0.52/0.75          | ((k2_relat_1 @ X23) = (k1_relat_1 @ (k2_funct_1 @ X23)))
% 0.52/0.75          | ~ (v1_funct_1 @ X23)
% 0.52/0.75          | ~ (v1_relat_1 @ X23))),
% 0.52/0.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.52/0.75  thf('91', plain,
% 0.52/0.75      (![X20 : $i]:
% 0.52/0.75         ((v1_relat_1 @ (k2_funct_1 @ X20))
% 0.52/0.75          | ~ (v1_funct_1 @ X20)
% 0.52/0.75          | ~ (v1_relat_1 @ X20))),
% 0.52/0.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.52/0.75  thf('92', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.52/0.75      inference('sup+', [status(thm)], ['13', '14'])).
% 0.52/0.75  thf('93', plain,
% 0.52/0.75      (![X20 : $i]:
% 0.52/0.75         ((v1_relat_1 @ (k2_funct_1 @ X20))
% 0.52/0.75          | ~ (v1_funct_1 @ X20)
% 0.52/0.75          | ~ (v1_relat_1 @ X20))),
% 0.52/0.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.52/0.75  thf('94', plain,
% 0.52/0.75      (![X23 : $i]:
% 0.52/0.75         (~ (v2_funct_1 @ X23)
% 0.52/0.75          | ((k2_relat_1 @ X23) = (k1_relat_1 @ (k2_funct_1 @ X23)))
% 0.52/0.75          | ~ (v1_funct_1 @ X23)
% 0.52/0.75          | ~ (v1_relat_1 @ X23))),
% 0.52/0.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.52/0.75  thf('95', plain,
% 0.52/0.75      (![X35 : $i]:
% 0.52/0.75         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 0.52/0.75          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.52/0.75      inference('demod', [status(thm)], ['50', '51'])).
% 0.52/0.75  thf('96', plain,
% 0.52/0.75      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.52/0.75         ((v4_relat_1 @ X25 @ X26)
% 0.52/0.75          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.52/0.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.52/0.75  thf('97', plain, (![X0 : $i]: (v4_relat_1 @ (k6_partfun1 @ X0) @ X0)),
% 0.52/0.75      inference('sup-', [status(thm)], ['95', '96'])).
% 0.52/0.75  thf('98', plain,
% 0.52/0.75      (![X2 : $i, X3 : $i]:
% 0.52/0.75         (~ (v4_relat_1 @ X2 @ X3)
% 0.52/0.75          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 0.52/0.75          | ~ (v1_relat_1 @ X2))),
% 0.52/0.75      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.52/0.75  thf('99', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.52/0.75          | (r1_tarski @ (k1_relat_1 @ (k6_partfun1 @ X0)) @ X0))),
% 0.52/0.75      inference('sup-', [status(thm)], ['97', '98'])).
% 0.52/0.75  thf('100', plain,
% 0.52/0.75      (![X35 : $i]:
% 0.52/0.75         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 0.52/0.75          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.52/0.75      inference('demod', [status(thm)], ['50', '51'])).
% 0.52/0.75  thf('101', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.52/0.75          | (v1_relat_1 @ X0)
% 0.52/0.75          | ~ (v1_relat_1 @ X1))),
% 0.52/0.75      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.52/0.75  thf('102', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X0))
% 0.52/0.75          | (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['100', '101'])).
% 0.52/0.75  thf('103', plain,
% 0.52/0.75      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.52/0.75      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.52/0.75  thf('104', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 0.52/0.75      inference('demod', [status(thm)], ['102', '103'])).
% 0.52/0.75  thf('105', plain,
% 0.52/0.75      (![X15 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X15)) = (X15))),
% 0.52/0.75      inference('demod', [status(thm)], ['56', '57'])).
% 0.52/0.75  thf('106', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.52/0.75      inference('demod', [status(thm)], ['99', '104', '105'])).
% 0.52/0.75  thf('107', plain,
% 0.52/0.75      (![X2 : $i, X3 : $i]:
% 0.52/0.75         (~ (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 0.52/0.75          | (v4_relat_1 @ X2 @ X3)
% 0.52/0.75          | ~ (v1_relat_1 @ X2))),
% 0.52/0.75      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.52/0.75  thf('108', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['106', '107'])).
% 0.52/0.75  thf('109', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.52/0.75          | ~ (v1_relat_1 @ X0)
% 0.52/0.75          | ~ (v1_funct_1 @ X0)
% 0.52/0.75          | ~ (v2_funct_1 @ X0)
% 0.52/0.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.52/0.75      inference('sup+', [status(thm)], ['94', '108'])).
% 0.52/0.75  thf('110', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         (~ (v1_relat_1 @ X0)
% 0.52/0.75          | ~ (v1_funct_1 @ X0)
% 0.52/0.75          | ~ (v2_funct_1 @ X0)
% 0.52/0.75          | ~ (v1_funct_1 @ X0)
% 0.52/0.75          | ~ (v1_relat_1 @ X0)
% 0.52/0.75          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['93', '109'])).
% 0.52/0.75  thf('111', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.52/0.75          | ~ (v2_funct_1 @ X0)
% 0.52/0.75          | ~ (v1_funct_1 @ X0)
% 0.52/0.75          | ~ (v1_relat_1 @ X0))),
% 0.52/0.75      inference('simplify', [status(thm)], ['110'])).
% 0.52/0.75  thf('112', plain,
% 0.52/0.75      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 0.52/0.75        | ~ (v1_relat_1 @ sk_C)
% 0.52/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.52/0.75        | ~ (v2_funct_1 @ sk_C))),
% 0.52/0.75      inference('sup+', [status(thm)], ['92', '111'])).
% 0.52/0.75  thf('113', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.75      inference('demod', [status(thm)], ['20', '21'])).
% 0.52/0.75  thf('114', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('115', plain, ((v2_funct_1 @ sk_C)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('116', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 0.52/0.75      inference('demod', [status(thm)], ['112', '113', '114', '115'])).
% 0.52/0.75  thf('117', plain,
% 0.52/0.75      (![X2 : $i, X3 : $i]:
% 0.52/0.75         (~ (v4_relat_1 @ X2 @ X3)
% 0.52/0.75          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 0.52/0.75          | ~ (v1_relat_1 @ X2))),
% 0.52/0.75      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.52/0.75  thf('118', plain,
% 0.52/0.75      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.52/0.75        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 0.52/0.75      inference('sup-', [status(thm)], ['116', '117'])).
% 0.52/0.75  thf('119', plain,
% 0.52/0.75      ((~ (v1_relat_1 @ sk_C)
% 0.52/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.52/0.75        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 0.52/0.75      inference('sup-', [status(thm)], ['91', '118'])).
% 0.52/0.75  thf('120', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.75      inference('demod', [status(thm)], ['20', '21'])).
% 0.52/0.75  thf('121', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('122', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 0.52/0.75      inference('demod', [status(thm)], ['119', '120', '121'])).
% 0.52/0.75  thf('123', plain,
% 0.52/0.75      (![X15 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X15)) = (X15))),
% 0.52/0.75      inference('demod', [status(thm)], ['56', '57'])).
% 0.52/0.75  thf('124', plain,
% 0.52/0.75      (![X2 : $i, X3 : $i]:
% 0.52/0.75         (~ (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 0.52/0.75          | (v4_relat_1 @ X2 @ X3)
% 0.52/0.75          | ~ (v1_relat_1 @ X2))),
% 0.52/0.75      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.52/0.75  thf('125', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         (~ (r1_tarski @ X0 @ X1)
% 0.52/0.75          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.52/0.75          | (v4_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.52/0.75      inference('sup-', [status(thm)], ['123', '124'])).
% 0.52/0.75  thf('126', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 0.52/0.75      inference('demod', [status(thm)], ['102', '103'])).
% 0.52/0.75  thf('127', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         (~ (r1_tarski @ X0 @ X1) | (v4_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 0.52/0.75      inference('demod', [status(thm)], ['125', '126'])).
% 0.52/0.75  thf('128', plain,
% 0.52/0.75      ((v4_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))) @ sk_B)),
% 0.52/0.75      inference('sup-', [status(thm)], ['122', '127'])).
% 0.52/0.75  thf('129', plain,
% 0.52/0.75      (![X10 : $i, X11 : $i]:
% 0.52/0.75         (((X10) = (k7_relat_1 @ X10 @ X11))
% 0.52/0.75          | ~ (v4_relat_1 @ X10 @ X11)
% 0.52/0.75          | ~ (v1_relat_1 @ X10))),
% 0.52/0.75      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.52/0.75  thf('130', plain,
% 0.52/0.75      ((~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 0.52/0.75        | ((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.52/0.75            = (k7_relat_1 @ 
% 0.52/0.75               (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))) @ sk_B)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['128', '129'])).
% 0.52/0.75  thf('131', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 0.52/0.75      inference('demod', [status(thm)], ['102', '103'])).
% 0.52/0.75  thf('132', plain,
% 0.52/0.75      (((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.52/0.75         = (k7_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))) @ 
% 0.52/0.75            sk_B))),
% 0.52/0.75      inference('demod', [status(thm)], ['130', '131'])).
% 0.52/0.75  thf('133', plain,
% 0.52/0.75      ((((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.52/0.75          = (k7_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ sk_B))
% 0.52/0.75        | ~ (v1_relat_1 @ sk_C)
% 0.52/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.52/0.75        | ~ (v2_funct_1 @ sk_C))),
% 0.52/0.75      inference('sup+', [status(thm)], ['90', '132'])).
% 0.52/0.75  thf('134', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.52/0.75      inference('sup+', [status(thm)], ['13', '14'])).
% 0.52/0.75  thf('135', plain, (![X0 : $i]: (v4_relat_1 @ (k6_partfun1 @ X0) @ X0)),
% 0.52/0.75      inference('sup-', [status(thm)], ['95', '96'])).
% 0.52/0.75  thf('136', plain,
% 0.52/0.75      (![X10 : $i, X11 : $i]:
% 0.52/0.75         (((X10) = (k7_relat_1 @ X10 @ X11))
% 0.52/0.75          | ~ (v4_relat_1 @ X10 @ X11)
% 0.52/0.75          | ~ (v1_relat_1 @ X10))),
% 0.52/0.75      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.52/0.75  thf('137', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.52/0.75          | ((k6_partfun1 @ X0) = (k7_relat_1 @ (k6_partfun1 @ X0) @ X0)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['135', '136'])).
% 0.52/0.75  thf('138', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 0.52/0.75      inference('demod', [status(thm)], ['102', '103'])).
% 0.52/0.75  thf('139', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         ((k6_partfun1 @ X0) = (k7_relat_1 @ (k6_partfun1 @ X0) @ X0))),
% 0.52/0.75      inference('demod', [status(thm)], ['137', '138'])).
% 0.52/0.75  thf('140', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.75      inference('demod', [status(thm)], ['20', '21'])).
% 0.52/0.75  thf('141', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('142', plain, ((v2_funct_1 @ sk_C)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('143', plain,
% 0.52/0.75      (((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.52/0.75         = (k6_partfun1 @ sk_B))),
% 0.52/0.75      inference('demod', [status(thm)],
% 0.52/0.75                ['133', '134', '139', '140', '141', '142'])).
% 0.52/0.75  thf('144', plain,
% 0.52/0.75      (![X15 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X15)) = (X15))),
% 0.52/0.75      inference('demod', [status(thm)], ['56', '57'])).
% 0.52/0.75  thf('145', plain,
% 0.52/0.75      (((k1_relat_1 @ (k6_partfun1 @ sk_B))
% 0.52/0.75         = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.52/0.75      inference('sup+', [status(thm)], ['143', '144'])).
% 0.52/0.75  thf('146', plain,
% 0.52/0.75      (![X15 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X15)) = (X15))),
% 0.52/0.75      inference('demod', [status(thm)], ['56', '57'])).
% 0.52/0.75  thf('147', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.52/0.75      inference('demod', [status(thm)], ['145', '146'])).
% 0.52/0.75  thf('148', plain,
% 0.52/0.75      (![X17 : $i]:
% 0.52/0.75         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X17)) @ X17) = (X17))
% 0.52/0.75          | ~ (v1_relat_1 @ X17))),
% 0.52/0.75      inference('demod', [status(thm)], ['77', '78'])).
% 0.52/0.75  thf('149', plain,
% 0.52/0.75      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 0.52/0.75          = (k2_funct_1 @ sk_C))
% 0.52/0.75        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.52/0.75      inference('sup+', [status(thm)], ['147', '148'])).
% 0.52/0.75  thf('150', plain,
% 0.52/0.75      ((~ (v1_relat_1 @ sk_C)
% 0.52/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.52/0.75        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 0.52/0.75            = (k2_funct_1 @ sk_C)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['89', '149'])).
% 0.52/0.75  thf('151', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.75      inference('demod', [status(thm)], ['20', '21'])).
% 0.52/0.75  thf('152', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('153', plain,
% 0.52/0.75      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 0.52/0.75         = (k2_funct_1 @ sk_C))),
% 0.52/0.75      inference('demod', [status(thm)], ['150', '151', '152'])).
% 0.52/0.75  thf(t55_relat_1, axiom,
% 0.52/0.75    (![A:$i]:
% 0.52/0.75     ( ( v1_relat_1 @ A ) =>
% 0.52/0.75       ( ![B:$i]:
% 0.52/0.75         ( ( v1_relat_1 @ B ) =>
% 0.52/0.75           ( ![C:$i]:
% 0.52/0.75             ( ( v1_relat_1 @ C ) =>
% 0.52/0.75               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.52/0.75                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.52/0.75  thf('154', plain,
% 0.52/0.75      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.52/0.75         (~ (v1_relat_1 @ X12)
% 0.52/0.75          | ((k5_relat_1 @ (k5_relat_1 @ X13 @ X12) @ X14)
% 0.52/0.75              = (k5_relat_1 @ X13 @ (k5_relat_1 @ X12 @ X14)))
% 0.52/0.75          | ~ (v1_relat_1 @ X14)
% 0.52/0.75          | ~ (v1_relat_1 @ X13))),
% 0.52/0.75      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.52/0.75  thf('155', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.52/0.75            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 0.52/0.75               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 0.52/0.75          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 0.52/0.75          | ~ (v1_relat_1 @ X0)
% 0.52/0.75          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.52/0.75      inference('sup+', [status(thm)], ['153', '154'])).
% 0.52/0.75  thf('156', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 0.52/0.75      inference('demod', [status(thm)], ['102', '103'])).
% 0.52/0.75  thf('157', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.52/0.75            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 0.52/0.75               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)))
% 0.52/0.75          | ~ (v1_relat_1 @ X0)
% 0.52/0.75          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.52/0.75      inference('demod', [status(thm)], ['155', '156'])).
% 0.52/0.75  thf('158', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         (~ (v1_relat_1 @ sk_C)
% 0.52/0.75          | ~ (v1_funct_1 @ sk_C)
% 0.52/0.75          | ~ (v1_relat_1 @ X0)
% 0.52/0.75          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.52/0.75              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 0.52/0.75                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 0.52/0.75      inference('sup-', [status(thm)], ['88', '157'])).
% 0.52/0.75  thf('159', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.75      inference('demod', [status(thm)], ['20', '21'])).
% 0.52/0.75  thf('160', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('161', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         (~ (v1_relat_1 @ X0)
% 0.52/0.75          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 0.52/0.75              = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 0.52/0.75                 (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))))),
% 0.52/0.75      inference('demod', [status(thm)], ['158', '159', '160'])).
% 0.52/0.75  thf('162', plain,
% 0.52/0.75      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.52/0.75          = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 0.52/0.75             (k6_partfun1 @ (k2_relat_1 @ sk_C))))
% 0.52/0.75        | ~ (v1_relat_1 @ sk_C)
% 0.52/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.52/0.75        | ~ (v2_funct_1 @ sk_C)
% 0.52/0.75        | ~ (v1_relat_1 @ sk_C))),
% 0.52/0.75      inference('sup+', [status(thm)], ['87', '161'])).
% 0.52/0.75  thf('163', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.52/0.75      inference('sup+', [status(thm)], ['13', '14'])).
% 0.52/0.75  thf('164', plain,
% 0.52/0.75      (![X15 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X15)) = (X15))),
% 0.52/0.75      inference('demod', [status(thm)], ['56', '57'])).
% 0.52/0.75  thf('165', plain,
% 0.52/0.75      (![X17 : $i]:
% 0.52/0.75         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X17)) @ X17) = (X17))
% 0.52/0.75          | ~ (v1_relat_1 @ X17))),
% 0.52/0.75      inference('demod', [status(thm)], ['77', '78'])).
% 0.52/0.75  thf('166', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 0.52/0.75            = (k6_partfun1 @ X0))
% 0.52/0.75          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.52/0.75      inference('sup+', [status(thm)], ['164', '165'])).
% 0.52/0.75  thf('167', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 0.52/0.75      inference('demod', [status(thm)], ['102', '103'])).
% 0.52/0.75  thf('168', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 0.52/0.75           = (k6_partfun1 @ X0))),
% 0.52/0.75      inference('demod', [status(thm)], ['166', '167'])).
% 0.52/0.75  thf('169', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.75      inference('demod', [status(thm)], ['20', '21'])).
% 0.52/0.75  thf('170', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('171', plain, ((v2_funct_1 @ sk_C)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('172', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.75      inference('demod', [status(thm)], ['20', '21'])).
% 0.52/0.75  thf('173', plain,
% 0.52/0.75      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 0.52/0.75      inference('demod', [status(thm)],
% 0.52/0.75                ['162', '163', '168', '169', '170', '171', '172'])).
% 0.52/0.75  thf('174', plain,
% 0.52/0.75      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.52/0.75         (~ (v1_relat_1 @ X12)
% 0.52/0.75          | ((k5_relat_1 @ (k5_relat_1 @ X13 @ X12) @ X14)
% 0.52/0.75              = (k5_relat_1 @ X13 @ (k5_relat_1 @ X12 @ X14)))
% 0.52/0.75          | ~ (v1_relat_1 @ X14)
% 0.52/0.75          | ~ (v1_relat_1 @ X13))),
% 0.52/0.75      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.52/0.75  thf('175', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 0.52/0.75            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 0.52/0.75          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.52/0.75          | ~ (v1_relat_1 @ X0)
% 0.52/0.75          | ~ (v1_relat_1 @ sk_C))),
% 0.52/0.75      inference('sup+', [status(thm)], ['173', '174'])).
% 0.52/0.75  thf('176', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.75      inference('demod', [status(thm)], ['20', '21'])).
% 0.52/0.75  thf('177', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 0.52/0.75            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 0.52/0.75          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.52/0.75          | ~ (v1_relat_1 @ X0))),
% 0.52/0.75      inference('demod', [status(thm)], ['175', '176'])).
% 0.52/0.75  thf('178', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         (~ (v1_relat_1 @ sk_C)
% 0.52/0.75          | ~ (v1_funct_1 @ sk_C)
% 0.52/0.75          | ~ (v1_relat_1 @ X0)
% 0.52/0.75          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 0.52/0.75              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 0.52/0.75      inference('sup-', [status(thm)], ['84', '177'])).
% 0.52/0.75  thf('179', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.75      inference('demod', [status(thm)], ['20', '21'])).
% 0.52/0.75  thf('180', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('181', plain,
% 0.52/0.75      (![X0 : $i]:
% 0.52/0.75         (~ (v1_relat_1 @ X0)
% 0.52/0.75          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 0.52/0.75              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 0.52/0.75      inference('demod', [status(thm)], ['178', '179', '180'])).
% 0.52/0.75  thf('182', plain,
% 0.52/0.75      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 0.52/0.75          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 0.52/0.75        | ~ (v1_relat_1 @ sk_D))),
% 0.52/0.75      inference('sup+', [status(thm)], ['83', '181'])).
% 0.52/0.75  thf('183', plain,
% 0.52/0.75      (![X20 : $i]:
% 0.52/0.75         ((v1_relat_1 @ (k2_funct_1 @ X20))
% 0.52/0.75          | ~ (v1_funct_1 @ X20)
% 0.52/0.75          | ~ (v1_relat_1 @ X20))),
% 0.52/0.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.52/0.75  thf('184', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.52/0.75      inference('sup-', [status(thm)], ['63', '64'])).
% 0.52/0.75  thf('185', plain,
% 0.52/0.75      (![X2 : $i, X3 : $i]:
% 0.52/0.75         (~ (v4_relat_1 @ X2 @ X3)
% 0.52/0.75          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 0.52/0.75          | ~ (v1_relat_1 @ X2))),
% 0.52/0.75      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.52/0.75  thf('186', plain,
% 0.52/0.75      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.52/0.75      inference('sup-', [status(thm)], ['184', '185'])).
% 0.52/0.75  thf('187', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.75      inference('demod', [status(thm)], ['20', '21'])).
% 0.52/0.75  thf('188', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.52/0.75      inference('demod', [status(thm)], ['186', '187'])).
% 0.52/0.75  thf('189', plain,
% 0.52/0.75      (![X23 : $i]:
% 0.52/0.75         (~ (v2_funct_1 @ X23)
% 0.52/0.75          | ((k1_relat_1 @ X23) = (k2_relat_1 @ (k2_funct_1 @ X23)))
% 0.52/0.75          | ~ (v1_funct_1 @ X23)
% 0.52/0.75          | ~ (v1_relat_1 @ X23))),
% 0.52/0.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.52/0.75  thf(t79_relat_1, axiom,
% 0.52/0.75    (![A:$i,B:$i]:
% 0.52/0.75     ( ( v1_relat_1 @ B ) =>
% 0.52/0.75       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.52/0.75         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.52/0.75  thf('190', plain,
% 0.52/0.75      (![X18 : $i, X19 : $i]:
% 0.52/0.75         (~ (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 0.52/0.75          | ((k5_relat_1 @ X18 @ (k6_relat_1 @ X19)) = (X18))
% 0.52/0.75          | ~ (v1_relat_1 @ X18))),
% 0.52/0.75      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.52/0.75  thf('191', plain, (![X48 : $i]: ((k6_partfun1 @ X48) = (k6_relat_1 @ X48))),
% 0.52/0.75      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.52/0.75  thf('192', plain,
% 0.52/0.75      (![X18 : $i, X19 : $i]:
% 0.52/0.75         (~ (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 0.52/0.75          | ((k5_relat_1 @ X18 @ (k6_partfun1 @ X19)) = (X18))
% 0.52/0.75          | ~ (v1_relat_1 @ X18))),
% 0.52/0.75      inference('demod', [status(thm)], ['190', '191'])).
% 0.52/0.75  thf('193', plain,
% 0.52/0.75      (![X0 : $i, X1 : $i]:
% 0.52/0.75         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.52/0.75          | ~ (v1_relat_1 @ X0)
% 0.52/0.75          | ~ (v1_funct_1 @ X0)
% 0.52/0.75          | ~ (v2_funct_1 @ X0)
% 0.52/0.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.52/0.75          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ X1))
% 0.52/0.75              = (k2_funct_1 @ X0)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['189', '192'])).
% 0.52/0.75  thf('194', plain,
% 0.52/0.75      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 0.52/0.75          = (k2_funct_1 @ sk_C))
% 0.52/0.75        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.52/0.75        | ~ (v2_funct_1 @ sk_C)
% 0.52/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.52/0.75        | ~ (v1_relat_1 @ sk_C))),
% 0.52/0.75      inference('sup-', [status(thm)], ['188', '193'])).
% 0.52/0.75  thf('195', plain, ((v2_funct_1 @ sk_C)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('196', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('197', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.75      inference('demod', [status(thm)], ['20', '21'])).
% 0.52/0.75  thf('198', plain,
% 0.52/0.75      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 0.52/0.75          = (k2_funct_1 @ sk_C))
% 0.52/0.75        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.52/0.75      inference('demod', [status(thm)], ['194', '195', '196', '197'])).
% 0.52/0.75  thf('199', plain,
% 0.52/0.75      ((~ (v1_relat_1 @ sk_C)
% 0.52/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.52/0.75        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 0.52/0.75            = (k2_funct_1 @ sk_C)))),
% 0.52/0.75      inference('sup-', [status(thm)], ['183', '198'])).
% 0.52/0.75  thf('200', plain, ((v1_relat_1 @ sk_C)),
% 0.52/0.75      inference('demod', [status(thm)], ['20', '21'])).
% 0.52/0.75  thf('201', plain, ((v1_funct_1 @ sk_C)),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('202', plain,
% 0.52/0.75      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 0.52/0.75         = (k2_funct_1 @ sk_C))),
% 0.52/0.75      inference('demod', [status(thm)], ['199', '200', '201'])).
% 0.52/0.75  thf('203', plain, ((v1_relat_1 @ sk_D)),
% 0.52/0.75      inference('demod', [status(thm)], ['7', '8'])).
% 0.52/0.75  thf('204', plain,
% 0.52/0.75      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (k2_funct_1 @ sk_C))),
% 0.52/0.75      inference('demod', [status(thm)], ['182', '202', '203'])).
% 0.52/0.75  thf('205', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.52/0.75      inference('sup+', [status(thm)], ['82', '204'])).
% 0.52/0.75  thf('206', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.52/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.75  thf('207', plain, ($false),
% 0.52/0.75      inference('simplify_reflect-', [status(thm)], ['205', '206'])).
% 0.52/0.75  
% 0.52/0.75  % SZS output end Refutation
% 0.52/0.75  
% 0.52/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
