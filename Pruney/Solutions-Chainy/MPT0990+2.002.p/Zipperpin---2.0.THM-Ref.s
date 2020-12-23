%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fXLQfQwnmx

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:53 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  299 (1657 expanded)
%              Number of leaves         :   48 ( 520 expanded)
%              Depth                    :   34
%              Number of atoms          : 2564 (38167 expanded)
%              Number of equality atoms :  160 (2836 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('6',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('7',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['4','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_D ) )
    | ( sk_B
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 )
        = ( k5_relat_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('20',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('21',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
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

thf('24',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('31',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( X26 = X29 )
      | ~ ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','32'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('34',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('35',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('36',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','18','37'])).

thf(t27_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k1_relat_1 @ B ) )
           => ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) )).

thf('39',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X16 ) @ ( k1_relat_1 @ X17 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) )
       != ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('40',plain,
    ( ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('41',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( B = k1_xboole_0 )
          | ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) )
              = ( k6_partfun1 @ A ) )
            & ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C )
              = ( k6_partfun1 @ B ) ) ) ) ) ) )).

thf('43',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ( ( k5_relat_1 @ X46 @ ( k2_funct_1 @ X46 ) )
        = ( k6_partfun1 @ X47 ) )
      | ~ ( v2_funct_1 @ X46 )
      | ( ( k2_relset_1 @ X47 @ X45 @ X46 )
       != X45 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('44',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('45',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ( ( k5_relat_1 @ X46 @ ( k2_funct_1 @ X46 ) )
        = ( k6_relat_1 @ X47 ) )
      | ~ ( v2_funct_1 @ X46 )
      | ( ( k2_relset_1 @ X47 @ X45 @ X46 )
       != X45 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47','48','49','50'])).

thf('52',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).

thf(t58_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) )
            = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('55',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X18 @ ( k2_funct_1 @ X18 ) ) )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('56',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_A ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57','60','61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('65',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X46 ) @ X46 )
        = ( k6_partfun1 @ X45 ) )
      | ~ ( v2_funct_1 @ X46 )
      | ( ( k2_relset_1 @ X47 @ X45 @ X46 )
       != X45 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('68',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('69',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X46 ) @ X46 )
        = ( k6_relat_1 @ X45 ) )
      | ~ ( v2_funct_1 @ X46 )
      | ( ( k2_relset_1 @ X47 @ X45 @ X46 )
       != X45 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','71','72','73','74'])).

thf('76',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

thf(t59_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) )
          & ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) )
            = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('79',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X19 ) @ X19 ) )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t59_funct_1])).

thf('80',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('82',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('83',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('86',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('88',plain,
    ( ( sk_A != sk_A )
    | ( r1_tarski @ sk_B @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['40','41','63','64','65','85','86','87'])).

thf('89',plain,(
    r1_tarski @ sk_B @ ( k1_relat_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['10','89'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('91',plain,(
    ! [X12: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X12 ) ) @ X12 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('92',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('94',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['17','18','37'])).

thf('96',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('97',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('101',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k2_funct_1 @ X14 )
        = ( k4_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('102',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('103',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('104',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('105',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('106',plain,(
    ! [X6: $i] :
      ( ( ( k2_relat_1 @ X6 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('108',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ( v4_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['106','110'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('112',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k2_funct_1 @ X14 )
        = ( k4_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('119',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('120',plain,(
    ! [X15: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('121',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X18 @ ( k2_funct_1 @ X18 ) ) )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t58_funct_1])).

thf('122',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X16 ) @ ( k1_relat_1 @ X17 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) )
       != ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['120','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['119','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['117','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_funct_1 @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['105','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['103','142'])).

thf('144',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('145',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['143','144','145','146'])).

thf('148',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('149',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('151',plain,(
    ! [X15: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('152',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).

thf('153',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X16 ) @ ( k1_relat_1 @ X17 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) )
       != ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_1])).

thf('154',plain,
    ( ( ( k1_relat_1 @ ( k6_relat_1 @ sk_A ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('156',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('158',plain,
    ( ( sk_A
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['154','155','156','157'])).

thf('159',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57','60','61','62'])).

thf('160',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['151','161'])).

thf('163',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('164',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['162','163','164'])).

thf('166',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['150','165'])).

thf('167',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('168',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['166','167','168'])).

thf('170',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('171',plain,(
    r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['149','171'])).

thf('173',plain,(
    ! [X12: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X12 ) ) @ X12 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('174',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['172','173'])).

thf('175',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['102','174'])).

thf('176',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('177',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['175','176','177'])).

thf('179',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k4_relat_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['101','178'])).

thf('180',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['80','81','82','83','84'])).

thf('181',plain,(
    ! [X6: $i] :
      ( ( ( k2_relat_1 @ X6 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('182',plain,(
    ! [X12: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X12 ) ) @ X12 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) )
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('184',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('185',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k4_relat_1 @ X0 ) )
        = ( k4_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['183','184'])).

thf('186',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k4_relat_1 @ sk_C ) )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['180','185'])).

thf('187',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('188',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k4_relat_1 @ sk_C ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('190',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['179','188','189','190','191'])).

thf('193',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['179','188','189','190','191'])).

thf('194',plain,
    ( ( k4_relat_1 @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['179','188','189','190','191'])).

thf('195',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('196',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['194','195'])).

thf('197',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('198',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['196','197','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['100','192','193','199'])).

thf('201',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['95','200'])).

thf('202',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('203',plain,(
    ! [X6: $i] :
      ( ( ( k1_relat_1 @ X6 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('204',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('205',plain,(
    ! [X6: $i] :
      ( ( ( k2_relat_1 @ X6 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('206',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('207',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('208',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57','60','61','62'])).

thf('209',plain,(
    ! [X6: $i] :
      ( ( ( k1_relat_1 @ X6 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('210',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k4_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('213',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['211','212'])).

thf('214',plain,
    ( ( v4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['208','213'])).

thf('215',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('216',plain,(
    v4_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['214','215'])).

thf('217',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('218',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['207','218'])).

thf('220',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['206','219'])).

thf('221',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('222',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['220','221'])).

thf('223',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ sk_A )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['205','222'])).

thf('224',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['204','223'])).

thf('225',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('226',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['224','225'])).

thf('227',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('228',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ( sk_A
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_A
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['203','228'])).

thf('230',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['56','57','60','61','62'])).

thf('231',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['107'])).

thf('232',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('233',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['229','230','231','232'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('234',plain,(
    ! [X13: $i] :
      ( ( ( k5_relat_1 @ X13 @ ( k6_relat_1 @ ( k2_relat_1 @ X13 ) ) )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('235',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['233','234'])).

thf('236',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['202','235'])).

thf('237',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('238',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['236','237'])).

thf('239',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['5','6'])).

thf('240',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_D )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['201','238','239'])).

thf('241',plain,
    ( sk_D
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['94','240'])).

thf('242',plain,(
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k2_funct_1 @ X14 )
        = ( k4_relat_1 @ X14 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('243',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,
    ( ( sk_D
     != ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('245',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['58','59'])).

thf('246',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    sk_D
 != ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['244','245','246','247'])).

thf('249',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['241','248'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fXLQfQwnmx
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:53:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.89/1.07  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.89/1.07  % Solved by: fo/fo7.sh
% 0.89/1.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.07  % done 1045 iterations in 0.613s
% 0.89/1.07  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.89/1.07  % SZS output start Refutation
% 0.89/1.07  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.89/1.07  thf(sk_D_type, type, sk_D: $i).
% 0.89/1.07  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.89/1.07  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.89/1.07  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.89/1.07  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.89/1.07  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.89/1.07  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.89/1.07  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.89/1.07  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.89/1.07  thf(sk_C_type, type, sk_C: $i).
% 0.89/1.07  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.89/1.07  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.89/1.07  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.07  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.89/1.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.89/1.07  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.89/1.07  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.89/1.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.89/1.07  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.07  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.89/1.07  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.89/1.07  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.89/1.07  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.89/1.07  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.89/1.07  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.89/1.07  thf(t36_funct_2, conjecture,
% 0.89/1.07    (![A:$i,B:$i,C:$i]:
% 0.89/1.07     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.89/1.07         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.07       ( ![D:$i]:
% 0.89/1.07         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.89/1.07             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.89/1.07           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.89/1.07               ( r2_relset_1 @
% 0.89/1.07                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.89/1.07                 ( k6_partfun1 @ A ) ) & 
% 0.89/1.07               ( v2_funct_1 @ C ) ) =>
% 0.89/1.07             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.89/1.07               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.89/1.07  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.07    (~( ![A:$i,B:$i,C:$i]:
% 0.89/1.07        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.89/1.07            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.07          ( ![D:$i]:
% 0.89/1.07            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.89/1.07                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.89/1.07              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.89/1.07                  ( r2_relset_1 @
% 0.89/1.07                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.89/1.07                    ( k6_partfun1 @ A ) ) & 
% 0.89/1.07                  ( v2_funct_1 @ C ) ) =>
% 0.89/1.07                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.89/1.07                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.89/1.07    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.89/1.07  thf('0', plain,
% 0.89/1.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf(cc2_relset_1, axiom,
% 0.89/1.07    (![A:$i,B:$i,C:$i]:
% 0.89/1.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.07       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.89/1.07  thf('1', plain,
% 0.89/1.07      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.89/1.07         ((v4_relat_1 @ X23 @ X24)
% 0.89/1.07          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.89/1.07      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.89/1.07  thf('2', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 0.89/1.07      inference('sup-', [status(thm)], ['0', '1'])).
% 0.89/1.07  thf(d18_relat_1, axiom,
% 0.89/1.07    (![A:$i,B:$i]:
% 0.89/1.07     ( ( v1_relat_1 @ B ) =>
% 0.89/1.07       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.89/1.07  thf('3', plain,
% 0.89/1.07      (![X3 : $i, X4 : $i]:
% 0.89/1.07         (~ (v4_relat_1 @ X3 @ X4)
% 0.89/1.07          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 0.89/1.07          | ~ (v1_relat_1 @ X3))),
% 0.89/1.07      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.89/1.07  thf('4', plain,
% 0.89/1.07      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 0.89/1.07      inference('sup-', [status(thm)], ['2', '3'])).
% 0.89/1.07  thf('5', plain,
% 0.89/1.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf(cc1_relset_1, axiom,
% 0.89/1.07    (![A:$i,B:$i,C:$i]:
% 0.89/1.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.07       ( v1_relat_1 @ C ) ))).
% 0.89/1.07  thf('6', plain,
% 0.89/1.07      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.89/1.07         ((v1_relat_1 @ X20)
% 0.89/1.07          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.89/1.07      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.89/1.07  thf('7', plain, ((v1_relat_1 @ sk_D)),
% 0.89/1.07      inference('sup-', [status(thm)], ['5', '6'])).
% 0.89/1.07  thf('8', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 0.89/1.07      inference('demod', [status(thm)], ['4', '7'])).
% 0.89/1.07  thf(d10_xboole_0, axiom,
% 0.89/1.07    (![A:$i,B:$i]:
% 0.89/1.07     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.89/1.07  thf('9', plain,
% 0.89/1.07      (![X0 : $i, X2 : $i]:
% 0.89/1.07         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.89/1.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.89/1.07  thf('10', plain,
% 0.89/1.07      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ sk_D))
% 0.89/1.07        | ((sk_B) = (k1_relat_1 @ sk_D)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['8', '9'])).
% 0.89/1.07  thf('11', plain,
% 0.89/1.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('12', plain,
% 0.89/1.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf(redefinition_k1_partfun1, axiom,
% 0.89/1.07    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.89/1.07     ( ( ( v1_funct_1 @ E ) & 
% 0.89/1.07         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.89/1.07         ( v1_funct_1 @ F ) & 
% 0.89/1.07         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.89/1.07       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.89/1.07  thf('13', plain,
% 0.89/1.07      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.89/1.07         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.89/1.07          | ~ (v1_funct_1 @ X38)
% 0.89/1.07          | ~ (v1_funct_1 @ X41)
% 0.89/1.07          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.89/1.07          | ((k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41)
% 0.89/1.07              = (k5_relat_1 @ X38 @ X41)))),
% 0.89/1.07      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.89/1.07  thf('14', plain,
% 0.89/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.07         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.89/1.07            = (k5_relat_1 @ sk_C @ X0))
% 0.89/1.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.89/1.07          | ~ (v1_funct_1 @ X0)
% 0.89/1.07          | ~ (v1_funct_1 @ sk_C))),
% 0.89/1.07      inference('sup-', [status(thm)], ['12', '13'])).
% 0.89/1.07  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('16', plain,
% 0.89/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.07         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.89/1.07            = (k5_relat_1 @ sk_C @ X0))
% 0.89/1.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.89/1.07          | ~ (v1_funct_1 @ X0))),
% 0.89/1.07      inference('demod', [status(thm)], ['14', '15'])).
% 0.89/1.07  thf('17', plain,
% 0.89/1.07      ((~ (v1_funct_1 @ sk_D)
% 0.89/1.07        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.89/1.07            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['11', '16'])).
% 0.89/1.07  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('19', plain,
% 0.89/1.07      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.89/1.07        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.89/1.07        (k6_partfun1 @ sk_A))),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf(redefinition_k6_partfun1, axiom,
% 0.89/1.07    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.89/1.07  thf('20', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 0.89/1.07      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.89/1.07  thf('21', plain,
% 0.89/1.07      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.89/1.07        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.89/1.07        (k6_relat_1 @ sk_A))),
% 0.89/1.07      inference('demod', [status(thm)], ['19', '20'])).
% 0.89/1.07  thf('22', plain,
% 0.89/1.07      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('23', plain,
% 0.89/1.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf(dt_k1_partfun1, axiom,
% 0.89/1.07    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.89/1.07     ( ( ( v1_funct_1 @ E ) & 
% 0.89/1.07         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.89/1.07         ( v1_funct_1 @ F ) & 
% 0.89/1.07         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.89/1.07       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.89/1.07         ( m1_subset_1 @
% 0.89/1.07           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.89/1.07           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.89/1.07  thf('24', plain,
% 0.89/1.07      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.89/1.07         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.89/1.07          | ~ (v1_funct_1 @ X30)
% 0.89/1.07          | ~ (v1_funct_1 @ X33)
% 0.89/1.07          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.89/1.07          | (m1_subset_1 @ (k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33) @ 
% 0.89/1.07             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X35))))),
% 0.89/1.07      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.89/1.07  thf('25', plain,
% 0.89/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.07         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.89/1.07           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.89/1.07          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.89/1.07          | ~ (v1_funct_1 @ X1)
% 0.89/1.07          | ~ (v1_funct_1 @ sk_C))),
% 0.89/1.07      inference('sup-', [status(thm)], ['23', '24'])).
% 0.89/1.07  thf('26', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('27', plain,
% 0.89/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.89/1.07         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.89/1.07           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.89/1.07          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.89/1.07          | ~ (v1_funct_1 @ X1))),
% 0.89/1.07      inference('demod', [status(thm)], ['25', '26'])).
% 0.89/1.07  thf('28', plain,
% 0.89/1.07      ((~ (v1_funct_1 @ sk_D)
% 0.89/1.07        | (m1_subset_1 @ 
% 0.89/1.07           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.89/1.07           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['22', '27'])).
% 0.89/1.07  thf('29', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('30', plain,
% 0.89/1.07      ((m1_subset_1 @ 
% 0.89/1.07        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.89/1.07        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.89/1.07      inference('demod', [status(thm)], ['28', '29'])).
% 0.89/1.07  thf(redefinition_r2_relset_1, axiom,
% 0.89/1.07    (![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.07     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.89/1.07         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.07       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.89/1.07  thf('31', plain,
% 0.89/1.07      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.89/1.07         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.89/1.07          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.89/1.07          | ((X26) = (X29))
% 0.89/1.07          | ~ (r2_relset_1 @ X27 @ X28 @ X26 @ X29))),
% 0.89/1.07      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.89/1.07  thf('32', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.89/1.07             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.89/1.07          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.89/1.07          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['30', '31'])).
% 0.89/1.07  thf('33', plain,
% 0.89/1.07      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.89/1.07           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.89/1.07        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.89/1.07            = (k6_relat_1 @ sk_A)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['21', '32'])).
% 0.89/1.07  thf(dt_k6_partfun1, axiom,
% 0.89/1.07    (![A:$i]:
% 0.89/1.07     ( ( m1_subset_1 @
% 0.89/1.07         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.89/1.07       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.89/1.07  thf('34', plain,
% 0.89/1.07      (![X37 : $i]:
% 0.89/1.07         (m1_subset_1 @ (k6_partfun1 @ X37) @ 
% 0.89/1.07          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 0.89/1.07      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.89/1.07  thf('35', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 0.89/1.07      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.89/1.07  thf('36', plain,
% 0.89/1.07      (![X37 : $i]:
% 0.89/1.07         (m1_subset_1 @ (k6_relat_1 @ X37) @ 
% 0.89/1.07          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 0.89/1.07      inference('demod', [status(thm)], ['34', '35'])).
% 0.89/1.07  thf('37', plain,
% 0.89/1.07      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.89/1.07         = (k6_relat_1 @ sk_A))),
% 0.89/1.07      inference('demod', [status(thm)], ['33', '36'])).
% 0.89/1.07  thf('38', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.89/1.07      inference('demod', [status(thm)], ['17', '18', '37'])).
% 0.89/1.07  thf(t27_funct_1, axiom,
% 0.89/1.07    (![A:$i]:
% 0.89/1.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.89/1.07       ( ![B:$i]:
% 0.89/1.07         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.89/1.07           ( ( ( k1_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k1_relat_1 @ B ) ) =>
% 0.89/1.07             ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.89/1.07  thf('39', plain,
% 0.89/1.07      (![X16 : $i, X17 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X16)
% 0.89/1.07          | ~ (v1_funct_1 @ X16)
% 0.89/1.07          | (r1_tarski @ (k2_relat_1 @ X16) @ (k1_relat_1 @ X17))
% 0.89/1.07          | ((k1_relat_1 @ (k5_relat_1 @ X16 @ X17)) != (k1_relat_1 @ X16))
% 0.89/1.07          | ~ (v1_funct_1 @ X17)
% 0.89/1.07          | ~ (v1_relat_1 @ X17))),
% 0.89/1.07      inference('cnf', [status(esa)], [t27_funct_1])).
% 0.89/1.07  thf('40', plain,
% 0.89/1.07      ((((k1_relat_1 @ (k6_relat_1 @ sk_A)) != (k1_relat_1 @ sk_C))
% 0.89/1.07        | ~ (v1_relat_1 @ sk_D)
% 0.89/1.07        | ~ (v1_funct_1 @ sk_D)
% 0.89/1.07        | (r1_tarski @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_D))
% 0.89/1.07        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.07        | ~ (v1_relat_1 @ sk_C))),
% 0.89/1.07      inference('sup-', [status(thm)], ['38', '39'])).
% 0.89/1.07  thf(t71_relat_1, axiom,
% 0.89/1.07    (![A:$i]:
% 0.89/1.07     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.89/1.07       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.89/1.07  thf('41', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.89/1.07      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.07  thf('42', plain,
% 0.89/1.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf(t35_funct_2, axiom,
% 0.89/1.07    (![A:$i,B:$i,C:$i]:
% 0.89/1.07     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.89/1.07         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.07       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.89/1.07         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.89/1.07           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.89/1.07             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.89/1.07  thf('43', plain,
% 0.89/1.07      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.89/1.07         (((X45) = (k1_xboole_0))
% 0.89/1.07          | ~ (v1_funct_1 @ X46)
% 0.89/1.07          | ~ (v1_funct_2 @ X46 @ X47 @ X45)
% 0.89/1.07          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 0.89/1.07          | ((k5_relat_1 @ X46 @ (k2_funct_1 @ X46)) = (k6_partfun1 @ X47))
% 0.89/1.07          | ~ (v2_funct_1 @ X46)
% 0.89/1.07          | ((k2_relset_1 @ X47 @ X45 @ X46) != (X45)))),
% 0.89/1.07      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.89/1.07  thf('44', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 0.89/1.07      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.89/1.07  thf('45', plain,
% 0.89/1.07      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.89/1.07         (((X45) = (k1_xboole_0))
% 0.89/1.07          | ~ (v1_funct_1 @ X46)
% 0.89/1.07          | ~ (v1_funct_2 @ X46 @ X47 @ X45)
% 0.89/1.07          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 0.89/1.07          | ((k5_relat_1 @ X46 @ (k2_funct_1 @ X46)) = (k6_relat_1 @ X47))
% 0.89/1.07          | ~ (v2_funct_1 @ X46)
% 0.89/1.07          | ((k2_relset_1 @ X47 @ X45 @ X46) != (X45)))),
% 0.89/1.07      inference('demod', [status(thm)], ['43', '44'])).
% 0.89/1.07  thf('46', plain,
% 0.89/1.07      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.89/1.07        | ~ (v2_funct_1 @ sk_C)
% 0.89/1.07        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 0.89/1.07        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.89/1.07        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.07        | ((sk_B) = (k1_xboole_0)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['42', '45'])).
% 0.89/1.07  thf('47', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('48', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('49', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('50', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('51', plain,
% 0.89/1.07      ((((sk_B) != (sk_B))
% 0.89/1.07        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 0.89/1.07        | ((sk_B) = (k1_xboole_0)))),
% 0.89/1.07      inference('demod', [status(thm)], ['46', '47', '48', '49', '50'])).
% 0.89/1.07  thf('52', plain,
% 0.89/1.07      ((((sk_B) = (k1_xboole_0))
% 0.89/1.07        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A)))),
% 0.89/1.07      inference('simplify', [status(thm)], ['51'])).
% 0.89/1.07  thf('53', plain, (((sk_B) != (k1_xboole_0))),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('54', plain,
% 0.89/1.07      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 0.89/1.07      inference('simplify_reflect-', [status(thm)], ['52', '53'])).
% 0.89/1.07  thf(t58_funct_1, axiom,
% 0.89/1.07    (![A:$i]:
% 0.89/1.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.89/1.07       ( ( v2_funct_1 @ A ) =>
% 0.89/1.07         ( ( ( k1_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.89/1.07             ( k1_relat_1 @ A ) ) & 
% 0.89/1.07           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) ) =
% 0.89/1.07             ( k1_relat_1 @ A ) ) ) ) ))).
% 0.89/1.07  thf('55', plain,
% 0.89/1.07      (![X18 : $i]:
% 0.89/1.07         (~ (v2_funct_1 @ X18)
% 0.89/1.07          | ((k2_relat_1 @ (k5_relat_1 @ X18 @ (k2_funct_1 @ X18)))
% 0.89/1.07              = (k1_relat_1 @ X18))
% 0.89/1.07          | ~ (v1_funct_1 @ X18)
% 0.89/1.07          | ~ (v1_relat_1 @ X18))),
% 0.89/1.07      inference('cnf', [status(esa)], [t58_funct_1])).
% 0.89/1.07  thf('56', plain,
% 0.89/1.07      ((((k2_relat_1 @ (k6_relat_1 @ sk_A)) = (k1_relat_1 @ sk_C))
% 0.89/1.07        | ~ (v1_relat_1 @ sk_C)
% 0.89/1.07        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.07        | ~ (v2_funct_1 @ sk_C))),
% 0.89/1.07      inference('sup+', [status(thm)], ['54', '55'])).
% 0.89/1.07  thf('57', plain, (![X11 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.89/1.07      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.07  thf('58', plain,
% 0.89/1.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('59', plain,
% 0.89/1.07      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.89/1.07         ((v1_relat_1 @ X20)
% 0.89/1.07          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.89/1.07      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.89/1.07  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.07      inference('sup-', [status(thm)], ['58', '59'])).
% 0.89/1.07  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('62', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('63', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.89/1.07      inference('demod', [status(thm)], ['56', '57', '60', '61', '62'])).
% 0.89/1.07  thf('64', plain, ((v1_relat_1 @ sk_D)),
% 0.89/1.07      inference('sup-', [status(thm)], ['5', '6'])).
% 0.89/1.07  thf('65', plain, ((v1_funct_1 @ sk_D)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('66', plain,
% 0.89/1.07      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('67', plain,
% 0.89/1.07      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.89/1.07         (((X45) = (k1_xboole_0))
% 0.89/1.07          | ~ (v1_funct_1 @ X46)
% 0.89/1.07          | ~ (v1_funct_2 @ X46 @ X47 @ X45)
% 0.89/1.07          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 0.89/1.07          | ((k5_relat_1 @ (k2_funct_1 @ X46) @ X46) = (k6_partfun1 @ X45))
% 0.89/1.07          | ~ (v2_funct_1 @ X46)
% 0.89/1.07          | ((k2_relset_1 @ X47 @ X45 @ X46) != (X45)))),
% 0.89/1.07      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.89/1.07  thf('68', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 0.89/1.07      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.89/1.07  thf('69', plain,
% 0.89/1.07      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.89/1.07         (((X45) = (k1_xboole_0))
% 0.89/1.07          | ~ (v1_funct_1 @ X46)
% 0.89/1.07          | ~ (v1_funct_2 @ X46 @ X47 @ X45)
% 0.89/1.07          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 0.89/1.07          | ((k5_relat_1 @ (k2_funct_1 @ X46) @ X46) = (k6_relat_1 @ X45))
% 0.89/1.07          | ~ (v2_funct_1 @ X46)
% 0.89/1.07          | ((k2_relset_1 @ X47 @ X45 @ X46) != (X45)))),
% 0.89/1.07      inference('demod', [status(thm)], ['67', '68'])).
% 0.89/1.07  thf('70', plain,
% 0.89/1.07      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.89/1.07        | ~ (v2_funct_1 @ sk_C)
% 0.89/1.07        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 0.89/1.07        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.89/1.07        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.07        | ((sk_B) = (k1_xboole_0)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['66', '69'])).
% 0.89/1.07  thf('71', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('72', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('73', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('75', plain,
% 0.89/1.07      ((((sk_B) != (sk_B))
% 0.89/1.07        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))
% 0.89/1.07        | ((sk_B) = (k1_xboole_0)))),
% 0.89/1.07      inference('demod', [status(thm)], ['70', '71', '72', '73', '74'])).
% 0.89/1.07  thf('76', plain,
% 0.89/1.07      ((((sk_B) = (k1_xboole_0))
% 0.89/1.07        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B)))),
% 0.89/1.07      inference('simplify', [status(thm)], ['75'])).
% 0.89/1.07  thf('77', plain, (((sk_B) != (k1_xboole_0))),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('78', plain,
% 0.89/1.07      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))),
% 0.89/1.07      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 0.89/1.07  thf(t59_funct_1, axiom,
% 0.89/1.07    (![A:$i]:
% 0.89/1.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.89/1.07       ( ( v2_funct_1 @ A ) =>
% 0.89/1.07         ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.89/1.07             ( k2_relat_1 @ A ) ) & 
% 0.89/1.07           ( ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) ) =
% 0.89/1.07             ( k2_relat_1 @ A ) ) ) ) ))).
% 0.89/1.07  thf('79', plain,
% 0.89/1.07      (![X19 : $i]:
% 0.89/1.07         (~ (v2_funct_1 @ X19)
% 0.89/1.07          | ((k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ X19) @ X19))
% 0.89/1.07              = (k2_relat_1 @ X19))
% 0.89/1.07          | ~ (v1_funct_1 @ X19)
% 0.89/1.07          | ~ (v1_relat_1 @ X19))),
% 0.89/1.07      inference('cnf', [status(esa)], [t59_funct_1])).
% 0.89/1.07  thf('80', plain,
% 0.89/1.07      ((((k2_relat_1 @ (k6_relat_1 @ sk_B)) = (k2_relat_1 @ sk_C))
% 0.89/1.07        | ~ (v1_relat_1 @ sk_C)
% 0.89/1.07        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.07        | ~ (v2_funct_1 @ sk_C))),
% 0.89/1.07      inference('sup+', [status(thm)], ['78', '79'])).
% 0.89/1.07  thf('81', plain, (![X11 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 0.89/1.07      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.07  thf('82', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.07      inference('sup-', [status(thm)], ['58', '59'])).
% 0.89/1.07  thf('83', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('84', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('85', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 0.89/1.07      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 0.89/1.07  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('87', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.07      inference('sup-', [status(thm)], ['58', '59'])).
% 0.89/1.07  thf('88', plain,
% 0.89/1.07      ((((sk_A) != (sk_A)) | (r1_tarski @ sk_B @ (k1_relat_1 @ sk_D)))),
% 0.89/1.07      inference('demod', [status(thm)],
% 0.89/1.07                ['40', '41', '63', '64', '65', '85', '86', '87'])).
% 0.89/1.07  thf('89', plain, ((r1_tarski @ sk_B @ (k1_relat_1 @ sk_D))),
% 0.89/1.07      inference('simplify', [status(thm)], ['88'])).
% 0.89/1.07  thf('90', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.89/1.07      inference('demod', [status(thm)], ['10', '89'])).
% 0.89/1.07  thf(t78_relat_1, axiom,
% 0.89/1.07    (![A:$i]:
% 0.89/1.07     ( ( v1_relat_1 @ A ) =>
% 0.89/1.07       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 0.89/1.07  thf('91', plain,
% 0.89/1.07      (![X12 : $i]:
% 0.89/1.07         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X12)) @ X12) = (X12))
% 0.89/1.07          | ~ (v1_relat_1 @ X12))),
% 0.89/1.07      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.89/1.07  thf('92', plain,
% 0.89/1.07      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D) = (sk_D))
% 0.89/1.07        | ~ (v1_relat_1 @ sk_D))),
% 0.89/1.07      inference('sup+', [status(thm)], ['90', '91'])).
% 0.89/1.07  thf('93', plain, ((v1_relat_1 @ sk_D)),
% 0.89/1.07      inference('sup-', [status(thm)], ['5', '6'])).
% 0.89/1.07  thf('94', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D) = (sk_D))),
% 0.89/1.07      inference('demod', [status(thm)], ['92', '93'])).
% 0.89/1.07  thf('95', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 0.89/1.07      inference('demod', [status(thm)], ['17', '18', '37'])).
% 0.89/1.07  thf('96', plain,
% 0.89/1.07      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_relat_1 @ sk_B))),
% 0.89/1.07      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 0.89/1.07  thf(t55_relat_1, axiom,
% 0.89/1.07    (![A:$i]:
% 0.89/1.07     ( ( v1_relat_1 @ A ) =>
% 0.89/1.07       ( ![B:$i]:
% 0.89/1.07         ( ( v1_relat_1 @ B ) =>
% 0.89/1.07           ( ![C:$i]:
% 0.89/1.07             ( ( v1_relat_1 @ C ) =>
% 0.89/1.07               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.89/1.07                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.89/1.07  thf('97', plain,
% 0.89/1.07      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X7)
% 0.89/1.07          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 0.89/1.07              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 0.89/1.07          | ~ (v1_relat_1 @ X9)
% 0.89/1.07          | ~ (v1_relat_1 @ X8))),
% 0.89/1.07      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.89/1.07  thf('98', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 0.89/1.07            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 0.89/1.07          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.07          | ~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ sk_C))),
% 0.89/1.07      inference('sup+', [status(thm)], ['96', '97'])).
% 0.89/1.07  thf('99', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.07      inference('sup-', [status(thm)], ['58', '59'])).
% 0.89/1.07  thf('100', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 0.89/1.07            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 0.89/1.07          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.07          | ~ (v1_relat_1 @ X0))),
% 0.89/1.07      inference('demod', [status(thm)], ['98', '99'])).
% 0.89/1.07  thf(d9_funct_1, axiom,
% 0.89/1.07    (![A:$i]:
% 0.89/1.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.89/1.07       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.89/1.07  thf('101', plain,
% 0.89/1.07      (![X14 : $i]:
% 0.89/1.07         (~ (v2_funct_1 @ X14)
% 0.89/1.07          | ((k2_funct_1 @ X14) = (k4_relat_1 @ X14))
% 0.89/1.07          | ~ (v1_funct_1 @ X14)
% 0.89/1.07          | ~ (v1_relat_1 @ X14))),
% 0.89/1.07      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.89/1.07  thf(dt_k2_funct_1, axiom,
% 0.89/1.07    (![A:$i]:
% 0.89/1.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.89/1.07       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.89/1.07         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.89/1.07  thf('102', plain,
% 0.89/1.07      (![X15 : $i]:
% 0.89/1.07         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.89/1.07          | ~ (v1_funct_1 @ X15)
% 0.89/1.07          | ~ (v1_relat_1 @ X15))),
% 0.89/1.07      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.89/1.07  thf('103', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 0.89/1.07      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 0.89/1.07  thf('104', plain,
% 0.89/1.07      (![X15 : $i]:
% 0.89/1.07         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.89/1.07          | ~ (v1_funct_1 @ X15)
% 0.89/1.07          | ~ (v1_relat_1 @ X15))),
% 0.89/1.07      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.89/1.07  thf('105', plain,
% 0.89/1.07      (![X15 : $i]:
% 0.89/1.07         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.89/1.07          | ~ (v1_funct_1 @ X15)
% 0.89/1.07          | ~ (v1_relat_1 @ X15))),
% 0.89/1.07      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.89/1.07  thf(t37_relat_1, axiom,
% 0.89/1.07    (![A:$i]:
% 0.89/1.07     ( ( v1_relat_1 @ A ) =>
% 0.89/1.07       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.89/1.07         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.89/1.07  thf('106', plain,
% 0.89/1.07      (![X6 : $i]:
% 0.89/1.07         (((k2_relat_1 @ X6) = (k1_relat_1 @ (k4_relat_1 @ X6)))
% 0.89/1.07          | ~ (v1_relat_1 @ X6))),
% 0.89/1.07      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.89/1.07  thf('107', plain,
% 0.89/1.07      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.89/1.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.89/1.07  thf('108', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.89/1.07      inference('simplify', [status(thm)], ['107'])).
% 0.89/1.07  thf('109', plain,
% 0.89/1.07      (![X3 : $i, X4 : $i]:
% 0.89/1.07         (~ (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 0.89/1.07          | (v4_relat_1 @ X3 @ X4)
% 0.89/1.07          | ~ (v1_relat_1 @ X3))),
% 0.89/1.07      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.89/1.07  thf('110', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['108', '109'])).
% 0.89/1.07  thf('111', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((v4_relat_1 @ (k4_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.89/1.07          | ~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.89/1.07      inference('sup+', [status(thm)], ['106', '110'])).
% 0.89/1.07  thf(dt_k4_relat_1, axiom,
% 0.89/1.07    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.89/1.07  thf('112', plain,
% 0.89/1.07      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.89/1.07      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.89/1.07  thf('113', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X0)
% 0.89/1.07          | (v4_relat_1 @ (k4_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.89/1.07      inference('clc', [status(thm)], ['111', '112'])).
% 0.89/1.07  thf('114', plain,
% 0.89/1.07      (![X3 : $i, X4 : $i]:
% 0.89/1.07         (~ (v4_relat_1 @ X3 @ X4)
% 0.89/1.07          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 0.89/1.07          | ~ (v1_relat_1 @ X3))),
% 0.89/1.07      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.89/1.07  thf('115', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.89/1.07          | (r1_tarski @ (k1_relat_1 @ (k4_relat_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['113', '114'])).
% 0.89/1.07  thf('116', plain,
% 0.89/1.07      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.89/1.07      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.89/1.07  thf('117', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((r1_tarski @ (k1_relat_1 @ (k4_relat_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.89/1.07          | ~ (v1_relat_1 @ X0))),
% 0.89/1.07      inference('clc', [status(thm)], ['115', '116'])).
% 0.89/1.07  thf('118', plain,
% 0.89/1.07      (![X14 : $i]:
% 0.89/1.07         (~ (v2_funct_1 @ X14)
% 0.89/1.07          | ((k2_funct_1 @ X14) = (k4_relat_1 @ X14))
% 0.89/1.07          | ~ (v1_funct_1 @ X14)
% 0.89/1.07          | ~ (v1_relat_1 @ X14))),
% 0.89/1.07      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.89/1.07  thf('119', plain,
% 0.89/1.07      (![X15 : $i]:
% 0.89/1.07         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.89/1.07          | ~ (v1_funct_1 @ X15)
% 0.89/1.07          | ~ (v1_relat_1 @ X15))),
% 0.89/1.07      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.89/1.07  thf('120', plain,
% 0.89/1.07      (![X15 : $i]:
% 0.89/1.07         ((v1_funct_1 @ (k2_funct_1 @ X15))
% 0.89/1.07          | ~ (v1_funct_1 @ X15)
% 0.89/1.07          | ~ (v1_relat_1 @ X15))),
% 0.89/1.07      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.89/1.07  thf('121', plain,
% 0.89/1.07      (![X18 : $i]:
% 0.89/1.07         (~ (v2_funct_1 @ X18)
% 0.89/1.07          | ((k1_relat_1 @ (k5_relat_1 @ X18 @ (k2_funct_1 @ X18)))
% 0.89/1.07              = (k1_relat_1 @ X18))
% 0.89/1.07          | ~ (v1_funct_1 @ X18)
% 0.89/1.07          | ~ (v1_relat_1 @ X18))),
% 0.89/1.07      inference('cnf', [status(esa)], [t58_funct_1])).
% 0.89/1.07  thf('122', plain,
% 0.89/1.07      (![X16 : $i, X17 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X16)
% 0.89/1.07          | ~ (v1_funct_1 @ X16)
% 0.89/1.07          | (r1_tarski @ (k2_relat_1 @ X16) @ (k1_relat_1 @ X17))
% 0.89/1.07          | ((k1_relat_1 @ (k5_relat_1 @ X16 @ X17)) != (k1_relat_1 @ X16))
% 0.89/1.07          | ~ (v1_funct_1 @ X17)
% 0.89/1.07          | ~ (v1_relat_1 @ X17))),
% 0.89/1.07      inference('cnf', [status(esa)], [t27_funct_1])).
% 0.89/1.07  thf('123', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.89/1.07          | ~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_funct_1 @ X0)
% 0.89/1.07          | ~ (v2_funct_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.89/1.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.07          | (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.89/1.07          | ~ (v1_funct_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ X0))),
% 0.89/1.07      inference('sup-', [status(thm)], ['121', '122'])).
% 0.89/1.07  thf('124', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.89/1.07          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.89/1.07          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.89/1.07          | ~ (v2_funct_1 @ X0)
% 0.89/1.07          | ~ (v1_funct_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ X0))),
% 0.89/1.07      inference('simplify', [status(thm)], ['123'])).
% 0.89/1.07  thf('125', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_funct_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_funct_1 @ X0)
% 0.89/1.07          | ~ (v2_funct_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.89/1.07          | (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['120', '124'])).
% 0.89/1.07  thf('126', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.89/1.07          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.89/1.07          | ~ (v2_funct_1 @ X0)
% 0.89/1.07          | ~ (v1_funct_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ X0))),
% 0.89/1.07      inference('simplify', [status(thm)], ['125'])).
% 0.89/1.07  thf('127', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_funct_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_funct_1 @ X0)
% 0.89/1.07          | ~ (v2_funct_1 @ X0)
% 0.89/1.07          | (r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['119', '126'])).
% 0.89/1.07  thf('128', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((r1_tarski @ (k2_relat_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.89/1.07          | ~ (v2_funct_1 @ X0)
% 0.89/1.07          | ~ (v1_funct_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ X0))),
% 0.89/1.07      inference('simplify', [status(thm)], ['127'])).
% 0.89/1.07  thf('129', plain,
% 0.89/1.07      (![X0 : $i, X2 : $i]:
% 0.89/1.07         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.89/1.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.89/1.07  thf('130', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_funct_1 @ X0)
% 0.89/1.07          | ~ (v2_funct_1 @ X0)
% 0.89/1.07          | ~ (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.89/1.07          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['128', '129'])).
% 0.89/1.07  thf('131', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (r1_tarski @ (k1_relat_1 @ (k4_relat_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.89/1.07          | ~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_funct_1 @ X0)
% 0.89/1.07          | ~ (v2_funct_1 @ X0)
% 0.89/1.07          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.89/1.07          | ~ (v2_funct_1 @ X0)
% 0.89/1.07          | ~ (v1_funct_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ X0))),
% 0.89/1.07      inference('sup-', [status(thm)], ['118', '130'])).
% 0.89/1.07  thf('132', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.89/1.07          | ~ (v2_funct_1 @ X0)
% 0.89/1.07          | ~ (v1_funct_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (r1_tarski @ (k1_relat_1 @ (k4_relat_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 0.89/1.07      inference('simplify', [status(thm)], ['131'])).
% 0.89/1.07  thf('133', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_funct_1 @ X0)
% 0.89/1.07          | ~ (v2_funct_1 @ X0)
% 0.89/1.07          | ((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['117', '132'])).
% 0.89/1.07  thf('134', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (((k1_relat_1 @ (k2_funct_1 @ X0)) = (k2_relat_1 @ X0))
% 0.89/1.07          | ~ (v2_funct_1 @ X0)
% 0.89/1.07          | ~ (v1_funct_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ X0))),
% 0.89/1.07      inference('simplify', [status(thm)], ['133'])).
% 0.89/1.07  thf('135', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['108', '109'])).
% 0.89/1.07  thf('136', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.89/1.07          | ~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_funct_1 @ X0)
% 0.89/1.07          | ~ (v2_funct_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.89/1.07      inference('sup+', [status(thm)], ['134', '135'])).
% 0.89/1.07  thf('137', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_funct_1 @ X0)
% 0.89/1.07          | ~ (v2_funct_1 @ X0)
% 0.89/1.07          | ~ (v1_funct_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ X0)
% 0.89/1.07          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['105', '136'])).
% 0.89/1.07  thf('138', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.89/1.07          | ~ (v2_funct_1 @ X0)
% 0.89/1.07          | ~ (v1_funct_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ X0))),
% 0.89/1.07      inference('simplify', [status(thm)], ['137'])).
% 0.89/1.07  thf('139', plain,
% 0.89/1.07      (![X3 : $i, X4 : $i]:
% 0.89/1.07         (~ (v4_relat_1 @ X3 @ X4)
% 0.89/1.07          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 0.89/1.07          | ~ (v1_relat_1 @ X3))),
% 0.89/1.07      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.89/1.07  thf('140', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_funct_1 @ X0)
% 0.89/1.07          | ~ (v2_funct_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.89/1.07          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['138', '139'])).
% 0.89/1.07  thf('141', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_funct_1 @ X0)
% 0.89/1.07          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.89/1.07          | ~ (v2_funct_1 @ X0)
% 0.89/1.07          | ~ (v1_funct_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ X0))),
% 0.89/1.07      inference('sup-', [status(thm)], ['104', '140'])).
% 0.89/1.07  thf('142', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v2_funct_1 @ X0)
% 0.89/1.07          | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k2_relat_1 @ X0))
% 0.89/1.07          | ~ (v1_funct_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ X0))),
% 0.89/1.07      inference('simplify', [status(thm)], ['141'])).
% 0.89/1.07  thf('143', plain,
% 0.89/1.07      (((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)
% 0.89/1.07        | ~ (v1_relat_1 @ sk_C)
% 0.89/1.07        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.07        | ~ (v2_funct_1 @ sk_C))),
% 0.89/1.07      inference('sup+', [status(thm)], ['103', '142'])).
% 0.89/1.07  thf('144', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.07      inference('sup-', [status(thm)], ['58', '59'])).
% 0.89/1.07  thf('145', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('146', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('147', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 0.89/1.07      inference('demod', [status(thm)], ['143', '144', '145', '146'])).
% 0.89/1.07  thf('148', plain,
% 0.89/1.07      (![X0 : $i, X2 : $i]:
% 0.89/1.07         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.89/1.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.89/1.07  thf('149', plain,
% 0.89/1.07      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.89/1.07        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['147', '148'])).
% 0.89/1.07  thf('150', plain,
% 0.89/1.07      (![X15 : $i]:
% 0.89/1.07         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.89/1.07          | ~ (v1_funct_1 @ X15)
% 0.89/1.07          | ~ (v1_relat_1 @ X15))),
% 0.89/1.07      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.89/1.07  thf('151', plain,
% 0.89/1.07      (![X15 : $i]:
% 0.89/1.07         ((v1_funct_1 @ (k2_funct_1 @ X15))
% 0.89/1.07          | ~ (v1_funct_1 @ X15)
% 0.89/1.07          | ~ (v1_relat_1 @ X15))),
% 0.89/1.07      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.89/1.07  thf('152', plain,
% 0.89/1.07      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 0.89/1.07      inference('simplify_reflect-', [status(thm)], ['52', '53'])).
% 0.89/1.07  thf('153', plain,
% 0.89/1.07      (![X16 : $i, X17 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X16)
% 0.89/1.07          | ~ (v1_funct_1 @ X16)
% 0.89/1.07          | (r1_tarski @ (k2_relat_1 @ X16) @ (k1_relat_1 @ X17))
% 0.89/1.07          | ((k1_relat_1 @ (k5_relat_1 @ X16 @ X17)) != (k1_relat_1 @ X16))
% 0.89/1.07          | ~ (v1_funct_1 @ X17)
% 0.89/1.07          | ~ (v1_relat_1 @ X17))),
% 0.89/1.07      inference('cnf', [status(esa)], [t27_funct_1])).
% 0.89/1.07  thf('154', plain,
% 0.89/1.07      ((((k1_relat_1 @ (k6_relat_1 @ sk_A)) != (k1_relat_1 @ sk_C))
% 0.89/1.07        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.07        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.07        | (r1_tarski @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.89/1.07        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.07        | ~ (v1_relat_1 @ sk_C))),
% 0.89/1.07      inference('sup-', [status(thm)], ['152', '153'])).
% 0.89/1.07  thf('155', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 0.89/1.07      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.89/1.07  thf('156', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('157', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.07      inference('sup-', [status(thm)], ['58', '59'])).
% 0.89/1.07  thf('158', plain,
% 0.89/1.07      ((((sk_A) != (k1_relat_1 @ sk_C))
% 0.89/1.07        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.07        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.07        | (r1_tarski @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.89/1.07      inference('demod', [status(thm)], ['154', '155', '156', '157'])).
% 0.89/1.07  thf('159', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.89/1.07      inference('demod', [status(thm)], ['56', '57', '60', '61', '62'])).
% 0.89/1.07  thf('160', plain,
% 0.89/1.07      ((((sk_A) != (sk_A))
% 0.89/1.07        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.07        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.07        | (r1_tarski @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.89/1.07      inference('demod', [status(thm)], ['158', '159'])).
% 0.89/1.07  thf('161', plain,
% 0.89/1.07      (((r1_tarski @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.89/1.07        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.07        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.89/1.07      inference('simplify', [status(thm)], ['160'])).
% 0.89/1.07  thf('162', plain,
% 0.89/1.07      ((~ (v1_relat_1 @ sk_C)
% 0.89/1.07        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.07        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.07        | (r1_tarski @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['151', '161'])).
% 0.89/1.07  thf('163', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.07      inference('sup-', [status(thm)], ['58', '59'])).
% 0.89/1.07  thf('164', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('165', plain,
% 0.89/1.07      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.89/1.07        | (r1_tarski @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.89/1.07      inference('demod', [status(thm)], ['162', '163', '164'])).
% 0.89/1.07  thf('166', plain,
% 0.89/1.07      ((~ (v1_relat_1 @ sk_C)
% 0.89/1.07        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.07        | (r1_tarski @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['150', '165'])).
% 0.89/1.07  thf('167', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.07      inference('sup-', [status(thm)], ['58', '59'])).
% 0.89/1.07  thf('168', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('169', plain,
% 0.89/1.07      ((r1_tarski @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.89/1.07      inference('demod', [status(thm)], ['166', '167', '168'])).
% 0.89/1.07  thf('170', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 0.89/1.07      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 0.89/1.07  thf('171', plain, ((r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.89/1.07      inference('demod', [status(thm)], ['169', '170'])).
% 0.89/1.07  thf('172', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.89/1.07      inference('demod', [status(thm)], ['149', '171'])).
% 0.89/1.07  thf('173', plain,
% 0.89/1.07      (![X12 : $i]:
% 0.89/1.07         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X12)) @ X12) = (X12))
% 0.89/1.07          | ~ (v1_relat_1 @ X12))),
% 0.89/1.07      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.89/1.07  thf('174', plain,
% 0.89/1.07      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 0.89/1.07          = (k2_funct_1 @ sk_C))
% 0.89/1.07        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.89/1.07      inference('sup+', [status(thm)], ['172', '173'])).
% 0.89/1.07  thf('175', plain,
% 0.89/1.07      ((~ (v1_relat_1 @ sk_C)
% 0.89/1.07        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.07        | ((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 0.89/1.07            = (k2_funct_1 @ sk_C)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['102', '174'])).
% 0.89/1.07  thf('176', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.07      inference('sup-', [status(thm)], ['58', '59'])).
% 0.89/1.07  thf('177', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('178', plain,
% 0.89/1.07      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 0.89/1.07         = (k2_funct_1 @ sk_C))),
% 0.89/1.07      inference('demod', [status(thm)], ['175', '176', '177'])).
% 0.89/1.07  thf('179', plain,
% 0.89/1.07      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k4_relat_1 @ sk_C))
% 0.89/1.07          = (k2_funct_1 @ sk_C))
% 0.89/1.07        | ~ (v1_relat_1 @ sk_C)
% 0.89/1.07        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.07        | ~ (v2_funct_1 @ sk_C))),
% 0.89/1.07      inference('sup+', [status(thm)], ['101', '178'])).
% 0.89/1.07  thf('180', plain, (((sk_B) = (k2_relat_1 @ sk_C))),
% 0.89/1.07      inference('demod', [status(thm)], ['80', '81', '82', '83', '84'])).
% 0.89/1.07  thf('181', plain,
% 0.89/1.07      (![X6 : $i]:
% 0.89/1.07         (((k2_relat_1 @ X6) = (k1_relat_1 @ (k4_relat_1 @ X6)))
% 0.89/1.07          | ~ (v1_relat_1 @ X6))),
% 0.89/1.07      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.89/1.07  thf('182', plain,
% 0.89/1.07      (![X12 : $i]:
% 0.89/1.07         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X12)) @ X12) = (X12))
% 0.89/1.07          | ~ (v1_relat_1 @ X12))),
% 0.89/1.07      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.89/1.07  thf('183', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k4_relat_1 @ X0))
% 0.89/1.07            = (k4_relat_1 @ X0))
% 0.89/1.07          | ~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.89/1.07      inference('sup+', [status(thm)], ['181', '182'])).
% 0.89/1.07  thf('184', plain,
% 0.89/1.07      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.89/1.07      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.89/1.07  thf('185', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X0)
% 0.89/1.07          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k4_relat_1 @ X0))
% 0.89/1.07              = (k4_relat_1 @ X0)))),
% 0.89/1.07      inference('clc', [status(thm)], ['183', '184'])).
% 0.89/1.07  thf('186', plain,
% 0.89/1.07      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k4_relat_1 @ sk_C))
% 0.89/1.07          = (k4_relat_1 @ sk_C))
% 0.89/1.07        | ~ (v1_relat_1 @ sk_C))),
% 0.89/1.07      inference('sup+', [status(thm)], ['180', '185'])).
% 0.89/1.07  thf('187', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.07      inference('sup-', [status(thm)], ['58', '59'])).
% 0.89/1.07  thf('188', plain,
% 0.89/1.07      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k4_relat_1 @ sk_C))
% 0.89/1.07         = (k4_relat_1 @ sk_C))),
% 0.89/1.07      inference('demod', [status(thm)], ['186', '187'])).
% 0.89/1.07  thf('189', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.07      inference('sup-', [status(thm)], ['58', '59'])).
% 0.89/1.07  thf('190', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('191', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('192', plain, (((k4_relat_1 @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.89/1.07      inference('demod', [status(thm)], ['179', '188', '189', '190', '191'])).
% 0.89/1.07  thf('193', plain, (((k4_relat_1 @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.89/1.07      inference('demod', [status(thm)], ['179', '188', '189', '190', '191'])).
% 0.89/1.07  thf('194', plain, (((k4_relat_1 @ sk_C) = (k2_funct_1 @ sk_C))),
% 0.89/1.07      inference('demod', [status(thm)], ['179', '188', '189', '190', '191'])).
% 0.89/1.07  thf('195', plain,
% 0.89/1.07      (![X15 : $i]:
% 0.89/1.07         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.89/1.07          | ~ (v1_funct_1 @ X15)
% 0.89/1.07          | ~ (v1_relat_1 @ X15))),
% 0.89/1.07      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.89/1.07  thf('196', plain,
% 0.89/1.07      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.89/1.07        | ~ (v1_relat_1 @ sk_C)
% 0.89/1.07        | ~ (v1_funct_1 @ sk_C))),
% 0.89/1.07      inference('sup+', [status(thm)], ['194', '195'])).
% 0.89/1.07  thf('197', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.07      inference('sup-', [status(thm)], ['58', '59'])).
% 0.89/1.07  thf('198', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('199', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.89/1.07      inference('demod', [status(thm)], ['196', '197', '198'])).
% 0.89/1.07  thf('200', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)
% 0.89/1.07            = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 0.89/1.07          | ~ (v1_relat_1 @ X0))),
% 0.89/1.07      inference('demod', [status(thm)], ['100', '192', '193', '199'])).
% 0.89/1.07  thf('201', plain,
% 0.89/1.07      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D)
% 0.89/1.07          = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_relat_1 @ sk_A)))
% 0.89/1.07        | ~ (v1_relat_1 @ sk_D))),
% 0.89/1.07      inference('sup+', [status(thm)], ['95', '200'])).
% 0.89/1.07  thf('202', plain,
% 0.89/1.07      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.89/1.07      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.89/1.07  thf('203', plain,
% 0.89/1.07      (![X6 : $i]:
% 0.89/1.07         (((k1_relat_1 @ X6) = (k2_relat_1 @ (k4_relat_1 @ X6)))
% 0.89/1.07          | ~ (v1_relat_1 @ X6))),
% 0.89/1.07      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.89/1.07  thf('204', plain,
% 0.89/1.07      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.89/1.07      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.89/1.07  thf('205', plain,
% 0.89/1.07      (![X6 : $i]:
% 0.89/1.07         (((k2_relat_1 @ X6) = (k1_relat_1 @ (k4_relat_1 @ X6)))
% 0.89/1.07          | ~ (v1_relat_1 @ X6))),
% 0.89/1.07      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.89/1.07  thf('206', plain,
% 0.89/1.07      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.89/1.07      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.89/1.07  thf('207', plain,
% 0.89/1.07      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.89/1.07      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.89/1.07  thf('208', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.89/1.07      inference('demod', [status(thm)], ['56', '57', '60', '61', '62'])).
% 0.89/1.07  thf('209', plain,
% 0.89/1.07      (![X6 : $i]:
% 0.89/1.07         (((k1_relat_1 @ X6) = (k2_relat_1 @ (k4_relat_1 @ X6)))
% 0.89/1.07          | ~ (v1_relat_1 @ X6))),
% 0.89/1.07      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.89/1.07  thf('210', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X0)
% 0.89/1.07          | (v4_relat_1 @ (k4_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.89/1.07      inference('clc', [status(thm)], ['111', '112'])).
% 0.89/1.07  thf('211', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         ((v4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.89/1.07          | ~ (v1_relat_1 @ X0)
% 0.89/1.07          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.89/1.07      inference('sup+', [status(thm)], ['209', '210'])).
% 0.89/1.07  thf('212', plain,
% 0.89/1.07      (![X5 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X5)) | ~ (v1_relat_1 @ X5))),
% 0.89/1.07      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.89/1.07  thf('213', plain,
% 0.89/1.07      (![X0 : $i]:
% 0.89/1.07         (~ (v1_relat_1 @ X0)
% 0.89/1.07          | (v4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.89/1.07      inference('clc', [status(thm)], ['211', '212'])).
% 0.89/1.07  thf('214', plain,
% 0.89/1.07      (((v4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_A)
% 0.89/1.07        | ~ (v1_relat_1 @ sk_C))),
% 0.89/1.07      inference('sup+', [status(thm)], ['208', '213'])).
% 0.89/1.07  thf('215', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.07      inference('sup-', [status(thm)], ['58', '59'])).
% 0.89/1.07  thf('216', plain, ((v4_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_A)),
% 0.89/1.07      inference('demod', [status(thm)], ['214', '215'])).
% 0.89/1.07  thf('217', plain,
% 0.89/1.07      (![X3 : $i, X4 : $i]:
% 0.89/1.07         (~ (v4_relat_1 @ X3 @ X4)
% 0.89/1.07          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 0.89/1.07          | ~ (v1_relat_1 @ X3))),
% 0.89/1.07      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.89/1.07  thf('218', plain,
% 0.89/1.07      ((~ (v1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.89/1.07        | (r1_tarski @ (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C))) @ sk_A))),
% 0.89/1.07      inference('sup-', [status(thm)], ['216', '217'])).
% 0.89/1.07  thf('219', plain,
% 0.89/1.07      ((~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.89/1.07        | (r1_tarski @ (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C))) @ sk_A))),
% 0.89/1.07      inference('sup-', [status(thm)], ['207', '218'])).
% 0.89/1.07  thf('220', plain,
% 0.89/1.07      ((~ (v1_relat_1 @ sk_C)
% 0.89/1.07        | (r1_tarski @ (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C))) @ sk_A))),
% 0.89/1.07      inference('sup-', [status(thm)], ['206', '219'])).
% 0.89/1.07  thf('221', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.07      inference('sup-', [status(thm)], ['58', '59'])).
% 0.89/1.07  thf('222', plain,
% 0.89/1.07      ((r1_tarski @ (k1_relat_1 @ (k4_relat_1 @ (k4_relat_1 @ sk_C))) @ sk_A)),
% 0.89/1.07      inference('demod', [status(thm)], ['220', '221'])).
% 0.89/1.07  thf('223', plain,
% 0.89/1.07      (((r1_tarski @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_A)
% 0.89/1.07        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.89/1.07      inference('sup+', [status(thm)], ['205', '222'])).
% 0.89/1.07  thf('224', plain,
% 0.89/1.07      ((~ (v1_relat_1 @ sk_C)
% 0.89/1.07        | (r1_tarski @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_A))),
% 0.89/1.07      inference('sup-', [status(thm)], ['204', '223'])).
% 0.89/1.07  thf('225', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.07      inference('sup-', [status(thm)], ['58', '59'])).
% 0.89/1.07  thf('226', plain, ((r1_tarski @ (k2_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_A)),
% 0.89/1.07      inference('demod', [status(thm)], ['224', '225'])).
% 0.89/1.07  thf('227', plain,
% 0.89/1.07      (![X0 : $i, X2 : $i]:
% 0.89/1.07         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.89/1.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.89/1.07  thf('228', plain,
% 0.89/1.07      ((~ (r1_tarski @ sk_A @ (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.89/1.07        | ((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['226', '227'])).
% 0.89/1.07  thf('229', plain,
% 0.89/1.07      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))
% 0.89/1.07        | ~ (v1_relat_1 @ sk_C)
% 0.89/1.07        | ((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C))))),
% 0.89/1.07      inference('sup-', [status(thm)], ['203', '228'])).
% 0.89/1.07  thf('230', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.89/1.07      inference('demod', [status(thm)], ['56', '57', '60', '61', '62'])).
% 0.89/1.07  thf('231', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.89/1.07      inference('simplify', [status(thm)], ['107'])).
% 0.89/1.07  thf('232', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.07      inference('sup-', [status(thm)], ['58', '59'])).
% 0.89/1.07  thf('233', plain, (((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.89/1.07      inference('demod', [status(thm)], ['229', '230', '231', '232'])).
% 0.89/1.07  thf(t80_relat_1, axiom,
% 0.89/1.07    (![A:$i]:
% 0.89/1.07     ( ( v1_relat_1 @ A ) =>
% 0.89/1.07       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.89/1.07  thf('234', plain,
% 0.89/1.07      (![X13 : $i]:
% 0.89/1.07         (((k5_relat_1 @ X13 @ (k6_relat_1 @ (k2_relat_1 @ X13))) = (X13))
% 0.89/1.07          | ~ (v1_relat_1 @ X13))),
% 0.89/1.07      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.89/1.07  thf('235', plain,
% 0.89/1.07      ((((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_relat_1 @ sk_A))
% 0.89/1.07          = (k4_relat_1 @ sk_C))
% 0.89/1.07        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.89/1.07      inference('sup+', [status(thm)], ['233', '234'])).
% 0.89/1.07  thf('236', plain,
% 0.89/1.07      ((~ (v1_relat_1 @ sk_C)
% 0.89/1.07        | ((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_relat_1 @ sk_A))
% 0.89/1.07            = (k4_relat_1 @ sk_C)))),
% 0.89/1.07      inference('sup-', [status(thm)], ['202', '235'])).
% 0.89/1.07  thf('237', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.07      inference('sup-', [status(thm)], ['58', '59'])).
% 0.89/1.07  thf('238', plain,
% 0.89/1.07      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_relat_1 @ sk_A))
% 0.89/1.07         = (k4_relat_1 @ sk_C))),
% 0.89/1.07      inference('demod', [status(thm)], ['236', '237'])).
% 0.89/1.07  thf('239', plain, ((v1_relat_1 @ sk_D)),
% 0.89/1.07      inference('sup-', [status(thm)], ['5', '6'])).
% 0.89/1.07  thf('240', plain,
% 0.89/1.07      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ sk_D) = (k4_relat_1 @ sk_C))),
% 0.89/1.07      inference('demod', [status(thm)], ['201', '238', '239'])).
% 0.89/1.07  thf('241', plain, (((sk_D) = (k4_relat_1 @ sk_C))),
% 0.89/1.07      inference('sup+', [status(thm)], ['94', '240'])).
% 0.89/1.07  thf('242', plain,
% 0.89/1.07      (![X14 : $i]:
% 0.89/1.07         (~ (v2_funct_1 @ X14)
% 0.89/1.07          | ((k2_funct_1 @ X14) = (k4_relat_1 @ X14))
% 0.89/1.07          | ~ (v1_funct_1 @ X14)
% 0.89/1.07          | ~ (v1_relat_1 @ X14))),
% 0.89/1.07      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.89/1.07  thf('243', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('244', plain,
% 0.89/1.07      ((((sk_D) != (k4_relat_1 @ sk_C))
% 0.89/1.07        | ~ (v1_relat_1 @ sk_C)
% 0.89/1.07        | ~ (v1_funct_1 @ sk_C)
% 0.89/1.07        | ~ (v2_funct_1 @ sk_C))),
% 0.89/1.07      inference('sup-', [status(thm)], ['242', '243'])).
% 0.89/1.07  thf('245', plain, ((v1_relat_1 @ sk_C)),
% 0.89/1.07      inference('sup-', [status(thm)], ['58', '59'])).
% 0.89/1.07  thf('246', plain, ((v1_funct_1 @ sk_C)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('247', plain, ((v2_funct_1 @ sk_C)),
% 0.89/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.07  thf('248', plain, (((sk_D) != (k4_relat_1 @ sk_C))),
% 0.89/1.07      inference('demod', [status(thm)], ['244', '245', '246', '247'])).
% 0.89/1.07  thf('249', plain, ($false),
% 0.89/1.07      inference('simplify_reflect-', [status(thm)], ['241', '248'])).
% 0.89/1.07  
% 0.89/1.07  % SZS output end Refutation
% 0.89/1.07  
% 0.89/1.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
