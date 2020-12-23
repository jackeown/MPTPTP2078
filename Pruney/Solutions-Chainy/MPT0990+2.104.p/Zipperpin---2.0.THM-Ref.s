%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zjuqUxKV6u

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:12 EST 2020

% Result     : Theorem 2.36s
% Output     : Refutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 551 expanded)
%              Number of leaves         :   46 ( 188 expanded)
%              Depth                    :   18
%              Number of atoms          : 1424 (10015 expanded)
%              Number of equality atoms :   85 ( 665 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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

thf('1',plain,(
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

thf('2',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) )
      | ( ( k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48 )
        = ( k5_relat_1 @ X45 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('18',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( X33 = X36 )
      | ~ ( r2_relset_1 @ X34 @ X35 @ X33 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('21',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('22',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['6','7','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['26','27'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('29',plain,(
    ! [X23: $i] :
      ( ~ ( v2_funct_1 @ X23 )
      | ( ( k2_funct_1 @ X23 )
        = ( k4_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('30',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X26 ) @ X26 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('35',plain,(
    ! [X51: $i] :
      ( ( k6_partfun1 @ X51 )
      = ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('36',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X26 ) @ X26 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X32 @ X30 )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('40',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['26','27'])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['37','42','43','44','45'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('47',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) @ X16 )
        = ( k5_relat_1 @ X15 @ ( k5_relat_1 @ X14 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('50',plain,(
    ! [X24: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('51',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['26','27'])).

thf('53',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['26','27'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','54','55'])).

thf('57',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['23','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('59',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v4_relat_1 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('60',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['58','59'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('61',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('67',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['62','67'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('69',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X21 ) @ X20 )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('70',plain,(
    ! [X51: $i] :
      ( ( k6_partfun1 @ X51 )
      = ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('71',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X21 ) @ X20 )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['65','66'])).

thf('74',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v4_relat_1 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('77',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('79',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['26','27'])).

thf('81',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X21 ) @ X20 )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('83',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C )
      = sk_C ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['26','27'])).

thf('85',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_A ) @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['83','84'])).

thf(t72_relat_1,axiom,(
    ! [A: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('86',plain,(
    ! [X19: $i] :
      ( ( k4_relat_1 @ ( k6_relat_1 @ X19 ) )
      = ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t72_relat_1])).

thf('87',plain,(
    ! [X51: $i] :
      ( ( k6_partfun1 @ X51 )
      = ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('88',plain,(
    ! [X51: $i] :
      ( ( k6_partfun1 @ X51 )
      = ( k6_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('89',plain,(
    ! [X19: $i] :
      ( ( k4_relat_1 @ ( k6_partfun1 @ X19 ) )
      = ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('90',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X12 ) @ ( k4_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X44: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X44 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('93',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['91','96'])).

thf('98',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('99',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relat_1 @ X25 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('100',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('102',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['26','27'])).

thf('103',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['100','101','102','103','104'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('107',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X20 ) @ X21 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X21 ) @ X20 )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k4_relat_1 @ sk_C ) )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['105','109'])).

thf('111',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('112',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k4_relat_1 @ sk_C ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X15 @ X14 ) @ X16 )
        = ( k5_relat_1 @ X15 @ ( k5_relat_1 @ X14 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('116',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_C ) ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['97','117'])).

thf('119',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['26','27'])).

thf('120',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ X0 ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['118','119','120'])).

thf('122',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['85','121'])).

thf('123',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k4_relat_1 @ sk_C ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('124',plain,
    ( ( k5_relat_1 @ ( k4_relat_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['65','66'])).

thf('126',plain,
    ( sk_D
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['57','74','124','125'])).

thf('127',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('129',plain,(
    sk_D
 != ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['126','129'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zjuqUxKV6u
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:00:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 2.36/2.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.36/2.55  % Solved by: fo/fo7.sh
% 2.36/2.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.36/2.55  % done 2463 iterations in 2.104s
% 2.36/2.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.36/2.55  % SZS output start Refutation
% 2.36/2.55  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.36/2.55  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.36/2.55  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.36/2.55  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.36/2.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.36/2.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.36/2.55  thf(sk_D_type, type, sk_D: $i).
% 2.36/2.55  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.36/2.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.36/2.55  thf(sk_A_type, type, sk_A: $i).
% 2.36/2.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.36/2.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.36/2.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.36/2.55  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.36/2.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.36/2.55  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.36/2.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.36/2.55  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.36/2.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.36/2.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.36/2.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.36/2.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.36/2.55  thf(sk_C_type, type, sk_C: $i).
% 2.36/2.55  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 2.36/2.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.36/2.55  thf(sk_B_type, type, sk_B: $i).
% 2.36/2.55  thf(t36_funct_2, conjecture,
% 2.36/2.55    (![A:$i,B:$i,C:$i]:
% 2.36/2.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.36/2.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.36/2.55       ( ![D:$i]:
% 2.36/2.55         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.36/2.55             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.36/2.55           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.36/2.55               ( r2_relset_1 @
% 2.36/2.55                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.36/2.55                 ( k6_partfun1 @ A ) ) & 
% 2.36/2.55               ( v2_funct_1 @ C ) ) =>
% 2.36/2.55             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.36/2.55               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 2.36/2.55  thf(zf_stmt_0, negated_conjecture,
% 2.36/2.55    (~( ![A:$i,B:$i,C:$i]:
% 2.36/2.55        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.36/2.55            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.36/2.55          ( ![D:$i]:
% 2.36/2.55            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.36/2.55                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.36/2.55              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.36/2.55                  ( r2_relset_1 @
% 2.36/2.55                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.36/2.55                    ( k6_partfun1 @ A ) ) & 
% 2.36/2.55                  ( v2_funct_1 @ C ) ) =>
% 2.36/2.55                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.36/2.55                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 2.36/2.55    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 2.36/2.55  thf('0', plain,
% 2.36/2.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.36/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.55  thf('1', plain,
% 2.36/2.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.36/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.55  thf(redefinition_k1_partfun1, axiom,
% 2.36/2.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.36/2.55     ( ( ( v1_funct_1 @ E ) & 
% 2.36/2.55         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.36/2.55         ( v1_funct_1 @ F ) & 
% 2.36/2.55         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.36/2.55       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.36/2.55  thf('2', plain,
% 2.36/2.55      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 2.36/2.55         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 2.36/2.55          | ~ (v1_funct_1 @ X45)
% 2.36/2.55          | ~ (v1_funct_1 @ X48)
% 2.36/2.55          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50)))
% 2.36/2.55          | ((k1_partfun1 @ X46 @ X47 @ X49 @ X50 @ X45 @ X48)
% 2.36/2.55              = (k5_relat_1 @ X45 @ X48)))),
% 2.36/2.55      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.36/2.55  thf('3', plain,
% 2.36/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.36/2.55         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.36/2.55            = (k5_relat_1 @ sk_C @ X0))
% 2.36/2.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.36/2.55          | ~ (v1_funct_1 @ X0)
% 2.36/2.55          | ~ (v1_funct_1 @ sk_C))),
% 2.36/2.55      inference('sup-', [status(thm)], ['1', '2'])).
% 2.36/2.55  thf('4', plain, ((v1_funct_1 @ sk_C)),
% 2.36/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.55  thf('5', plain,
% 2.36/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.36/2.55         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.36/2.55            = (k5_relat_1 @ sk_C @ X0))
% 2.36/2.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.36/2.55          | ~ (v1_funct_1 @ X0))),
% 2.36/2.55      inference('demod', [status(thm)], ['3', '4'])).
% 2.36/2.55  thf('6', plain,
% 2.36/2.55      ((~ (v1_funct_1 @ sk_D)
% 2.36/2.55        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.36/2.55            = (k5_relat_1 @ sk_C @ sk_D)))),
% 2.36/2.55      inference('sup-', [status(thm)], ['0', '5'])).
% 2.36/2.55  thf('7', plain, ((v1_funct_1 @ sk_D)),
% 2.36/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.55  thf('8', plain,
% 2.36/2.55      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.36/2.55        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.36/2.55        (k6_partfun1 @ sk_A))),
% 2.36/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.55  thf('9', plain,
% 2.36/2.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.36/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.55  thf('10', plain,
% 2.36/2.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.36/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.55  thf(dt_k1_partfun1, axiom,
% 2.36/2.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.36/2.55     ( ( ( v1_funct_1 @ E ) & 
% 2.36/2.55         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.36/2.55         ( v1_funct_1 @ F ) & 
% 2.36/2.55         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.36/2.55       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.36/2.55         ( m1_subset_1 @
% 2.36/2.55           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.36/2.55           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.36/2.55  thf('11', plain,
% 2.36/2.55      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 2.36/2.55         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 2.36/2.55          | ~ (v1_funct_1 @ X37)
% 2.36/2.55          | ~ (v1_funct_1 @ X40)
% 2.36/2.55          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 2.36/2.55          | (m1_subset_1 @ (k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40) @ 
% 2.36/2.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X42))))),
% 2.36/2.55      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.36/2.55  thf('12', plain,
% 2.36/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.36/2.55         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.36/2.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.36/2.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.36/2.55          | ~ (v1_funct_1 @ X1)
% 2.36/2.55          | ~ (v1_funct_1 @ sk_C))),
% 2.36/2.55      inference('sup-', [status(thm)], ['10', '11'])).
% 2.36/2.55  thf('13', plain, ((v1_funct_1 @ sk_C)),
% 2.36/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.55  thf('14', plain,
% 2.36/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.36/2.55         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.36/2.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.36/2.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.36/2.55          | ~ (v1_funct_1 @ X1))),
% 2.36/2.55      inference('demod', [status(thm)], ['12', '13'])).
% 2.36/2.55  thf('15', plain,
% 2.36/2.55      ((~ (v1_funct_1 @ sk_D)
% 2.36/2.55        | (m1_subset_1 @ 
% 2.36/2.55           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.36/2.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.36/2.55      inference('sup-', [status(thm)], ['9', '14'])).
% 2.36/2.55  thf('16', plain, ((v1_funct_1 @ sk_D)),
% 2.36/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.55  thf('17', plain,
% 2.36/2.55      ((m1_subset_1 @ 
% 2.36/2.55        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.36/2.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.36/2.55      inference('demod', [status(thm)], ['15', '16'])).
% 2.36/2.55  thf(redefinition_r2_relset_1, axiom,
% 2.36/2.55    (![A:$i,B:$i,C:$i,D:$i]:
% 2.36/2.55     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.36/2.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.36/2.55       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.36/2.55  thf('18', plain,
% 2.36/2.55      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 2.36/2.55         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 2.36/2.55          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 2.36/2.55          | ((X33) = (X36))
% 2.36/2.55          | ~ (r2_relset_1 @ X34 @ X35 @ X33 @ X36))),
% 2.36/2.55      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.36/2.55  thf('19', plain,
% 2.36/2.55      (![X0 : $i]:
% 2.36/2.55         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.36/2.55             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 2.36/2.55          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 2.36/2.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.36/2.55      inference('sup-', [status(thm)], ['17', '18'])).
% 2.36/2.55  thf('20', plain,
% 2.36/2.55      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 2.36/2.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.36/2.55        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.36/2.55            = (k6_partfun1 @ sk_A)))),
% 2.36/2.55      inference('sup-', [status(thm)], ['8', '19'])).
% 2.36/2.55  thf(dt_k6_partfun1, axiom,
% 2.36/2.55    (![A:$i]:
% 2.36/2.55     ( ( m1_subset_1 @
% 2.36/2.55         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 2.36/2.55       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 2.36/2.55  thf('21', plain,
% 2.36/2.55      (![X44 : $i]:
% 2.36/2.55         (m1_subset_1 @ (k6_partfun1 @ X44) @ 
% 2.36/2.55          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X44)))),
% 2.36/2.55      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 2.36/2.55  thf('22', plain,
% 2.36/2.55      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.36/2.55         = (k6_partfun1 @ sk_A))),
% 2.36/2.55      inference('demod', [status(thm)], ['20', '21'])).
% 2.36/2.55  thf('23', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 2.36/2.55      inference('demod', [status(thm)], ['6', '7', '22'])).
% 2.36/2.55  thf('24', plain,
% 2.36/2.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.36/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.55  thf(cc2_relat_1, axiom,
% 2.36/2.55    (![A:$i]:
% 2.36/2.55     ( ( v1_relat_1 @ A ) =>
% 2.36/2.55       ( ![B:$i]:
% 2.36/2.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.36/2.55  thf('25', plain,
% 2.36/2.55      (![X3 : $i, X4 : $i]:
% 2.36/2.55         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.36/2.55          | (v1_relat_1 @ X3)
% 2.36/2.55          | ~ (v1_relat_1 @ X4))),
% 2.36/2.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.36/2.55  thf('26', plain,
% 2.36/2.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 2.36/2.55      inference('sup-', [status(thm)], ['24', '25'])).
% 2.36/2.55  thf(fc6_relat_1, axiom,
% 2.36/2.55    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.36/2.55  thf('27', plain,
% 2.36/2.55      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 2.36/2.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.36/2.55  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 2.36/2.55      inference('demod', [status(thm)], ['26', '27'])).
% 2.36/2.55  thf(d9_funct_1, axiom,
% 2.36/2.55    (![A:$i]:
% 2.36/2.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.36/2.55       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 2.36/2.55  thf('29', plain,
% 2.36/2.55      (![X23 : $i]:
% 2.36/2.55         (~ (v2_funct_1 @ X23)
% 2.36/2.55          | ((k2_funct_1 @ X23) = (k4_relat_1 @ X23))
% 2.36/2.55          | ~ (v1_funct_1 @ X23)
% 2.36/2.55          | ~ (v1_relat_1 @ X23))),
% 2.36/2.55      inference('cnf', [status(esa)], [d9_funct_1])).
% 2.36/2.55  thf('30', plain,
% 2.36/2.55      ((~ (v1_funct_1 @ sk_C)
% 2.36/2.55        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 2.36/2.55        | ~ (v2_funct_1 @ sk_C))),
% 2.36/2.55      inference('sup-', [status(thm)], ['28', '29'])).
% 2.36/2.55  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 2.36/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.55  thf('32', plain, ((v2_funct_1 @ sk_C)),
% 2.36/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.55  thf('33', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 2.36/2.55      inference('demod', [status(thm)], ['30', '31', '32'])).
% 2.36/2.55  thf(t61_funct_1, axiom,
% 2.36/2.55    (![A:$i]:
% 2.36/2.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.36/2.55       ( ( v2_funct_1 @ A ) =>
% 2.36/2.55         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 2.36/2.55             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 2.36/2.55           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 2.36/2.55             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.36/2.55  thf('34', plain,
% 2.36/2.55      (![X26 : $i]:
% 2.36/2.55         (~ (v2_funct_1 @ X26)
% 2.36/2.55          | ((k5_relat_1 @ (k2_funct_1 @ X26) @ X26)
% 2.36/2.55              = (k6_relat_1 @ (k2_relat_1 @ X26)))
% 2.36/2.55          | ~ (v1_funct_1 @ X26)
% 2.36/2.55          | ~ (v1_relat_1 @ X26))),
% 2.36/2.55      inference('cnf', [status(esa)], [t61_funct_1])).
% 2.36/2.55  thf(redefinition_k6_partfun1, axiom,
% 2.36/2.55    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.36/2.55  thf('35', plain, (![X51 : $i]: ((k6_partfun1 @ X51) = (k6_relat_1 @ X51))),
% 2.36/2.55      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.36/2.55  thf('36', plain,
% 2.36/2.55      (![X26 : $i]:
% 2.36/2.55         (~ (v2_funct_1 @ X26)
% 2.36/2.55          | ((k5_relat_1 @ (k2_funct_1 @ X26) @ X26)
% 2.36/2.55              = (k6_partfun1 @ (k2_relat_1 @ X26)))
% 2.36/2.55          | ~ (v1_funct_1 @ X26)
% 2.36/2.55          | ~ (v1_relat_1 @ X26))),
% 2.36/2.55      inference('demod', [status(thm)], ['34', '35'])).
% 2.36/2.55  thf('37', plain,
% 2.36/2.55      ((((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C)
% 2.36/2.55          = (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 2.36/2.55        | ~ (v1_relat_1 @ sk_C)
% 2.36/2.55        | ~ (v1_funct_1 @ sk_C)
% 2.36/2.55        | ~ (v2_funct_1 @ sk_C))),
% 2.36/2.55      inference('sup+', [status(thm)], ['33', '36'])).
% 2.36/2.55  thf('38', plain,
% 2.36/2.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.36/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.55  thf(redefinition_k2_relset_1, axiom,
% 2.36/2.55    (![A:$i,B:$i,C:$i]:
% 2.36/2.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.36/2.55       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.36/2.55  thf('39', plain,
% 2.36/2.55      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.36/2.55         (((k2_relset_1 @ X31 @ X32 @ X30) = (k2_relat_1 @ X30))
% 2.36/2.55          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 2.36/2.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.36/2.55  thf('40', plain,
% 2.36/2.55      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 2.36/2.55      inference('sup-', [status(thm)], ['38', '39'])).
% 2.36/2.55  thf('41', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.36/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.55  thf('42', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.36/2.55      inference('sup+', [status(thm)], ['40', '41'])).
% 2.36/2.55  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 2.36/2.55      inference('demod', [status(thm)], ['26', '27'])).
% 2.36/2.55  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 2.36/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.55  thf('45', plain, ((v2_funct_1 @ sk_C)),
% 2.36/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.55  thf('46', plain,
% 2.36/2.55      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 2.36/2.55      inference('demod', [status(thm)], ['37', '42', '43', '44', '45'])).
% 2.36/2.55  thf(t55_relat_1, axiom,
% 2.36/2.55    (![A:$i]:
% 2.36/2.55     ( ( v1_relat_1 @ A ) =>
% 2.36/2.55       ( ![B:$i]:
% 2.36/2.55         ( ( v1_relat_1 @ B ) =>
% 2.36/2.55           ( ![C:$i]:
% 2.36/2.55             ( ( v1_relat_1 @ C ) =>
% 2.36/2.55               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 2.36/2.55                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 2.36/2.55  thf('47', plain,
% 2.36/2.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.36/2.55         (~ (v1_relat_1 @ X14)
% 2.36/2.55          | ((k5_relat_1 @ (k5_relat_1 @ X15 @ X14) @ X16)
% 2.36/2.55              = (k5_relat_1 @ X15 @ (k5_relat_1 @ X14 @ X16)))
% 2.36/2.55          | ~ (v1_relat_1 @ X16)
% 2.36/2.55          | ~ (v1_relat_1 @ X15))),
% 2.36/2.55      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.36/2.55  thf('48', plain,
% 2.36/2.55      (![X0 : $i]:
% 2.36/2.55         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 2.36/2.55            = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 2.36/2.55          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 2.36/2.55          | ~ (v1_relat_1 @ X0)
% 2.36/2.55          | ~ (v1_relat_1 @ sk_C))),
% 2.36/2.55      inference('sup+', [status(thm)], ['46', '47'])).
% 2.36/2.55  thf('49', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 2.36/2.55      inference('demod', [status(thm)], ['30', '31', '32'])).
% 2.36/2.55  thf(dt_k2_funct_1, axiom,
% 2.36/2.55    (![A:$i]:
% 2.36/2.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.36/2.55       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.36/2.55         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.36/2.55  thf('50', plain,
% 2.36/2.55      (![X24 : $i]:
% 2.36/2.55         ((v1_relat_1 @ (k2_funct_1 @ X24))
% 2.36/2.55          | ~ (v1_funct_1 @ X24)
% 2.36/2.55          | ~ (v1_relat_1 @ X24))),
% 2.36/2.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.36/2.55  thf('51', plain,
% 2.36/2.55      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 2.36/2.55        | ~ (v1_relat_1 @ sk_C)
% 2.36/2.55        | ~ (v1_funct_1 @ sk_C))),
% 2.36/2.55      inference('sup+', [status(thm)], ['49', '50'])).
% 2.36/2.55  thf('52', plain, ((v1_relat_1 @ sk_C)),
% 2.36/2.55      inference('demod', [status(thm)], ['26', '27'])).
% 2.36/2.55  thf('53', plain, ((v1_funct_1 @ sk_C)),
% 2.36/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.55  thf('54', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 2.36/2.55      inference('demod', [status(thm)], ['51', '52', '53'])).
% 2.36/2.55  thf('55', plain, ((v1_relat_1 @ sk_C)),
% 2.36/2.55      inference('demod', [status(thm)], ['26', '27'])).
% 2.36/2.55  thf('56', plain,
% 2.36/2.55      (![X0 : $i]:
% 2.36/2.55         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 2.36/2.55            = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 2.36/2.55          | ~ (v1_relat_1 @ X0))),
% 2.36/2.55      inference('demod', [status(thm)], ['48', '54', '55'])).
% 2.36/2.55  thf('57', plain,
% 2.36/2.55      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 2.36/2.55          = (k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 2.36/2.55        | ~ (v1_relat_1 @ sk_D))),
% 2.36/2.55      inference('sup+', [status(thm)], ['23', '56'])).
% 2.36/2.55  thf('58', plain,
% 2.36/2.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.36/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.55  thf(cc2_relset_1, axiom,
% 2.36/2.55    (![A:$i,B:$i,C:$i]:
% 2.36/2.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.36/2.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.36/2.55  thf('59', plain,
% 2.36/2.55      (![X27 : $i, X28 : $i, X29 : $i]:
% 2.36/2.55         ((v4_relat_1 @ X27 @ X28)
% 2.36/2.55          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 2.36/2.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.36/2.55  thf('60', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 2.36/2.55      inference('sup-', [status(thm)], ['58', '59'])).
% 2.36/2.55  thf(d18_relat_1, axiom,
% 2.36/2.55    (![A:$i,B:$i]:
% 2.36/2.55     ( ( v1_relat_1 @ B ) =>
% 2.36/2.55       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 2.36/2.55  thf('61', plain,
% 2.36/2.55      (![X5 : $i, X6 : $i]:
% 2.36/2.55         (~ (v4_relat_1 @ X5 @ X6)
% 2.36/2.55          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 2.36/2.55          | ~ (v1_relat_1 @ X5))),
% 2.36/2.55      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.36/2.55  thf('62', plain,
% 2.36/2.55      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 2.36/2.55      inference('sup-', [status(thm)], ['60', '61'])).
% 2.36/2.55  thf('63', plain,
% 2.36/2.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.36/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.55  thf('64', plain,
% 2.36/2.55      (![X3 : $i, X4 : $i]:
% 2.36/2.55         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.36/2.55          | (v1_relat_1 @ X3)
% 2.36/2.55          | ~ (v1_relat_1 @ X4))),
% 2.36/2.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.36/2.55  thf('65', plain,
% 2.36/2.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 2.36/2.55      inference('sup-', [status(thm)], ['63', '64'])).
% 2.36/2.55  thf('66', plain,
% 2.36/2.55      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 2.36/2.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.36/2.55  thf('67', plain, ((v1_relat_1 @ sk_D)),
% 2.36/2.55      inference('demod', [status(thm)], ['65', '66'])).
% 2.36/2.55  thf('68', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 2.36/2.55      inference('demod', [status(thm)], ['62', '67'])).
% 2.36/2.55  thf(t77_relat_1, axiom,
% 2.36/2.55    (![A:$i,B:$i]:
% 2.36/2.55     ( ( v1_relat_1 @ B ) =>
% 2.36/2.55       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 2.36/2.55         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 2.36/2.55  thf('69', plain,
% 2.36/2.55      (![X20 : $i, X21 : $i]:
% 2.36/2.55         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 2.36/2.55          | ((k5_relat_1 @ (k6_relat_1 @ X21) @ X20) = (X20))
% 2.36/2.56          | ~ (v1_relat_1 @ X20))),
% 2.36/2.56      inference('cnf', [status(esa)], [t77_relat_1])).
% 2.36/2.56  thf('70', plain, (![X51 : $i]: ((k6_partfun1 @ X51) = (k6_relat_1 @ X51))),
% 2.36/2.56      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.36/2.56  thf('71', plain,
% 2.36/2.56      (![X20 : $i, X21 : $i]:
% 2.36/2.56         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 2.36/2.56          | ((k5_relat_1 @ (k6_partfun1 @ X21) @ X20) = (X20))
% 2.36/2.56          | ~ (v1_relat_1 @ X20))),
% 2.36/2.56      inference('demod', [status(thm)], ['69', '70'])).
% 2.36/2.56  thf('72', plain,
% 2.36/2.56      ((~ (v1_relat_1 @ sk_D)
% 2.36/2.56        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D)))),
% 2.36/2.56      inference('sup-', [status(thm)], ['68', '71'])).
% 2.36/2.56  thf('73', plain, ((v1_relat_1 @ sk_D)),
% 2.36/2.56      inference('demod', [status(thm)], ['65', '66'])).
% 2.36/2.56  thf('74', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 2.36/2.56      inference('demod', [status(thm)], ['72', '73'])).
% 2.36/2.56  thf('75', plain,
% 2.36/2.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.36/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.56  thf('76', plain,
% 2.36/2.56      (![X27 : $i, X28 : $i, X29 : $i]:
% 2.36/2.56         ((v4_relat_1 @ X27 @ X28)
% 2.36/2.56          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 2.36/2.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.36/2.56  thf('77', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 2.36/2.56      inference('sup-', [status(thm)], ['75', '76'])).
% 2.36/2.56  thf('78', plain,
% 2.36/2.56      (![X5 : $i, X6 : $i]:
% 2.36/2.56         (~ (v4_relat_1 @ X5 @ X6)
% 2.36/2.56          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 2.36/2.56          | ~ (v1_relat_1 @ X5))),
% 2.36/2.56      inference('cnf', [status(esa)], [d18_relat_1])).
% 2.36/2.56  thf('79', plain,
% 2.36/2.56      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 2.36/2.56      inference('sup-', [status(thm)], ['77', '78'])).
% 2.36/2.56  thf('80', plain, ((v1_relat_1 @ sk_C)),
% 2.36/2.56      inference('demod', [status(thm)], ['26', '27'])).
% 2.36/2.56  thf('81', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 2.36/2.56      inference('demod', [status(thm)], ['79', '80'])).
% 2.36/2.56  thf('82', plain,
% 2.36/2.56      (![X20 : $i, X21 : $i]:
% 2.36/2.56         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 2.36/2.56          | ((k5_relat_1 @ (k6_partfun1 @ X21) @ X20) = (X20))
% 2.36/2.56          | ~ (v1_relat_1 @ X20))),
% 2.36/2.56      inference('demod', [status(thm)], ['69', '70'])).
% 2.36/2.56  thf('83', plain,
% 2.36/2.56      ((~ (v1_relat_1 @ sk_C)
% 2.36/2.56        | ((k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C) = (sk_C)))),
% 2.36/2.56      inference('sup-', [status(thm)], ['81', '82'])).
% 2.36/2.56  thf('84', plain, ((v1_relat_1 @ sk_C)),
% 2.36/2.56      inference('demod', [status(thm)], ['26', '27'])).
% 2.36/2.56  thf('85', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_A) @ sk_C) = (sk_C))),
% 2.36/2.56      inference('demod', [status(thm)], ['83', '84'])).
% 2.36/2.56  thf(t72_relat_1, axiom,
% 2.36/2.56    (![A:$i]: ( ( k4_relat_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 2.36/2.56  thf('86', plain,
% 2.36/2.56      (![X19 : $i]: ((k4_relat_1 @ (k6_relat_1 @ X19)) = (k6_relat_1 @ X19))),
% 2.36/2.56      inference('cnf', [status(esa)], [t72_relat_1])).
% 2.36/2.56  thf('87', plain, (![X51 : $i]: ((k6_partfun1 @ X51) = (k6_relat_1 @ X51))),
% 2.36/2.56      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.36/2.56  thf('88', plain, (![X51 : $i]: ((k6_partfun1 @ X51) = (k6_relat_1 @ X51))),
% 2.36/2.56      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.36/2.56  thf('89', plain,
% 2.36/2.56      (![X19 : $i]: ((k4_relat_1 @ (k6_partfun1 @ X19)) = (k6_partfun1 @ X19))),
% 2.36/2.56      inference('demod', [status(thm)], ['86', '87', '88'])).
% 2.36/2.56  thf(t54_relat_1, axiom,
% 2.36/2.56    (![A:$i]:
% 2.36/2.56     ( ( v1_relat_1 @ A ) =>
% 2.36/2.56       ( ![B:$i]:
% 2.36/2.56         ( ( v1_relat_1 @ B ) =>
% 2.36/2.56           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 2.36/2.56             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 2.36/2.56  thf('90', plain,
% 2.36/2.56      (![X12 : $i, X13 : $i]:
% 2.36/2.56         (~ (v1_relat_1 @ X12)
% 2.36/2.56          | ((k4_relat_1 @ (k5_relat_1 @ X13 @ X12))
% 2.36/2.56              = (k5_relat_1 @ (k4_relat_1 @ X12) @ (k4_relat_1 @ X13)))
% 2.36/2.56          | ~ (v1_relat_1 @ X13))),
% 2.36/2.56      inference('cnf', [status(esa)], [t54_relat_1])).
% 2.36/2.56  thf('91', plain,
% 2.36/2.56      (![X0 : $i, X1 : $i]:
% 2.36/2.56         (((k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 2.36/2.56            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_partfun1 @ X0)))
% 2.36/2.56          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 2.36/2.56          | ~ (v1_relat_1 @ X1))),
% 2.36/2.56      inference('sup+', [status(thm)], ['89', '90'])).
% 2.36/2.56  thf('92', plain,
% 2.36/2.56      (![X44 : $i]:
% 2.36/2.56         (m1_subset_1 @ (k6_partfun1 @ X44) @ 
% 2.36/2.56          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X44)))),
% 2.36/2.56      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 2.36/2.56  thf('93', plain,
% 2.36/2.56      (![X3 : $i, X4 : $i]:
% 2.36/2.56         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 2.36/2.56          | (v1_relat_1 @ X3)
% 2.36/2.56          | ~ (v1_relat_1 @ X4))),
% 2.36/2.56      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.36/2.56  thf('94', plain,
% 2.36/2.56      (![X0 : $i]:
% 2.36/2.56         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X0))
% 2.36/2.56          | (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 2.36/2.56      inference('sup-', [status(thm)], ['92', '93'])).
% 2.36/2.56  thf('95', plain,
% 2.36/2.56      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 2.36/2.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.36/2.56  thf('96', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 2.36/2.56      inference('demod', [status(thm)], ['94', '95'])).
% 2.36/2.56  thf('97', plain,
% 2.36/2.56      (![X0 : $i, X1 : $i]:
% 2.36/2.56         (((k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 2.36/2.56            = (k5_relat_1 @ (k4_relat_1 @ X1) @ (k6_partfun1 @ X0)))
% 2.36/2.56          | ~ (v1_relat_1 @ X1))),
% 2.36/2.56      inference('demod', [status(thm)], ['91', '96'])).
% 2.36/2.56  thf('98', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 2.36/2.56      inference('demod', [status(thm)], ['30', '31', '32'])).
% 2.36/2.56  thf(t55_funct_1, axiom,
% 2.36/2.56    (![A:$i]:
% 2.36/2.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.36/2.56       ( ( v2_funct_1 @ A ) =>
% 2.36/2.56         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.36/2.56           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.36/2.56  thf('99', plain,
% 2.36/2.56      (![X25 : $i]:
% 2.36/2.56         (~ (v2_funct_1 @ X25)
% 2.36/2.56          | ((k2_relat_1 @ X25) = (k1_relat_1 @ (k2_funct_1 @ X25)))
% 2.36/2.56          | ~ (v1_funct_1 @ X25)
% 2.36/2.56          | ~ (v1_relat_1 @ X25))),
% 2.36/2.56      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.36/2.56  thf('100', plain,
% 2.36/2.56      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 2.36/2.56        | ~ (v1_relat_1 @ sk_C)
% 2.36/2.56        | ~ (v1_funct_1 @ sk_C)
% 2.36/2.56        | ~ (v2_funct_1 @ sk_C))),
% 2.36/2.56      inference('sup+', [status(thm)], ['98', '99'])).
% 2.36/2.56  thf('101', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.36/2.56      inference('sup+', [status(thm)], ['40', '41'])).
% 2.36/2.56  thf('102', plain, ((v1_relat_1 @ sk_C)),
% 2.36/2.56      inference('demod', [status(thm)], ['26', '27'])).
% 2.36/2.56  thf('103', plain, ((v1_funct_1 @ sk_C)),
% 2.36/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.56  thf('104', plain, ((v2_funct_1 @ sk_C)),
% 2.36/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.56  thf('105', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 2.36/2.56      inference('demod', [status(thm)], ['100', '101', '102', '103', '104'])).
% 2.36/2.56  thf(d10_xboole_0, axiom,
% 2.36/2.56    (![A:$i,B:$i]:
% 2.36/2.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.36/2.56  thf('106', plain,
% 2.36/2.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.36/2.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.36/2.56  thf('107', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.36/2.56      inference('simplify', [status(thm)], ['106'])).
% 2.36/2.56  thf('108', plain,
% 2.36/2.56      (![X20 : $i, X21 : $i]:
% 2.36/2.56         (~ (r1_tarski @ (k1_relat_1 @ X20) @ X21)
% 2.36/2.56          | ((k5_relat_1 @ (k6_partfun1 @ X21) @ X20) = (X20))
% 2.36/2.56          | ~ (v1_relat_1 @ X20))),
% 2.36/2.56      inference('demod', [status(thm)], ['69', '70'])).
% 2.36/2.56  thf('109', plain,
% 2.36/2.56      (![X0 : $i]:
% 2.36/2.56         (~ (v1_relat_1 @ X0)
% 2.36/2.56          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 2.36/2.56      inference('sup-', [status(thm)], ['107', '108'])).
% 2.36/2.56  thf('110', plain,
% 2.36/2.56      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k4_relat_1 @ sk_C))
% 2.36/2.56          = (k4_relat_1 @ sk_C))
% 2.36/2.56        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 2.36/2.56      inference('sup+', [status(thm)], ['105', '109'])).
% 2.36/2.56  thf('111', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 2.36/2.56      inference('demod', [status(thm)], ['51', '52', '53'])).
% 2.36/2.56  thf('112', plain,
% 2.36/2.56      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k4_relat_1 @ sk_C))
% 2.36/2.56         = (k4_relat_1 @ sk_C))),
% 2.36/2.56      inference('demod', [status(thm)], ['110', '111'])).
% 2.36/2.56  thf('113', plain,
% 2.36/2.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.36/2.56         (~ (v1_relat_1 @ X14)
% 2.36/2.56          | ((k5_relat_1 @ (k5_relat_1 @ X15 @ X14) @ X16)
% 2.36/2.56              = (k5_relat_1 @ X15 @ (k5_relat_1 @ X14 @ X16)))
% 2.36/2.56          | ~ (v1_relat_1 @ X16)
% 2.36/2.56          | ~ (v1_relat_1 @ X15))),
% 2.36/2.56      inference('cnf', [status(esa)], [t55_relat_1])).
% 2.36/2.56  thf('114', plain,
% 2.36/2.56      (![X0 : $i]:
% 2.36/2.56         (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ X0)
% 2.36/2.56            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 2.36/2.56               (k5_relat_1 @ (k4_relat_1 @ sk_C) @ X0)))
% 2.36/2.56          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 2.36/2.56          | ~ (v1_relat_1 @ X0)
% 2.36/2.56          | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 2.36/2.56      inference('sup+', [status(thm)], ['112', '113'])).
% 2.36/2.56  thf('115', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 2.36/2.56      inference('demod', [status(thm)], ['94', '95'])).
% 2.36/2.56  thf('116', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 2.36/2.56      inference('demod', [status(thm)], ['51', '52', '53'])).
% 2.36/2.56  thf('117', plain,
% 2.36/2.56      (![X0 : $i]:
% 2.36/2.56         (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ X0)
% 2.36/2.56            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 2.36/2.56               (k5_relat_1 @ (k4_relat_1 @ sk_C) @ X0)))
% 2.36/2.56          | ~ (v1_relat_1 @ X0))),
% 2.36/2.56      inference('demod', [status(thm)], ['114', '115', '116'])).
% 2.36/2.56  thf('118', plain,
% 2.36/2.56      (![X0 : $i]:
% 2.36/2.56         (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_partfun1 @ X0))
% 2.36/2.56            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 2.36/2.56               (k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_C))))
% 2.36/2.56          | ~ (v1_relat_1 @ sk_C)
% 2.36/2.56          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 2.36/2.56      inference('sup+', [status(thm)], ['97', '117'])).
% 2.36/2.56  thf('119', plain, ((v1_relat_1 @ sk_C)),
% 2.36/2.56      inference('demod', [status(thm)], ['26', '27'])).
% 2.36/2.56  thf('120', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 2.36/2.56      inference('demod', [status(thm)], ['94', '95'])).
% 2.36/2.56  thf('121', plain,
% 2.36/2.56      (![X0 : $i]:
% 2.36/2.56         ((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_partfun1 @ X0))
% 2.36/2.56           = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 2.36/2.56              (k4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_C))))),
% 2.36/2.56      inference('demod', [status(thm)], ['118', '119', '120'])).
% 2.36/2.56  thf('122', plain,
% 2.36/2.56      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 2.36/2.56         = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k4_relat_1 @ sk_C)))),
% 2.36/2.56      inference('sup+', [status(thm)], ['85', '121'])).
% 2.36/2.56  thf('123', plain,
% 2.36/2.56      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k4_relat_1 @ sk_C))
% 2.36/2.56         = (k4_relat_1 @ sk_C))),
% 2.36/2.56      inference('demod', [status(thm)], ['110', '111'])).
% 2.36/2.56  thf('124', plain,
% 2.36/2.56      (((k5_relat_1 @ (k4_relat_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 2.36/2.56         = (k4_relat_1 @ sk_C))),
% 2.36/2.56      inference('demod', [status(thm)], ['122', '123'])).
% 2.36/2.56  thf('125', plain, ((v1_relat_1 @ sk_D)),
% 2.36/2.56      inference('demod', [status(thm)], ['65', '66'])).
% 2.36/2.56  thf('126', plain, (((sk_D) = (k4_relat_1 @ sk_C))),
% 2.36/2.56      inference('demod', [status(thm)], ['57', '74', '124', '125'])).
% 2.36/2.56  thf('127', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 2.36/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.36/2.56  thf('128', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 2.36/2.56      inference('demod', [status(thm)], ['30', '31', '32'])).
% 2.36/2.56  thf('129', plain, (((sk_D) != (k4_relat_1 @ sk_C))),
% 2.36/2.56      inference('demod', [status(thm)], ['127', '128'])).
% 2.36/2.56  thf('130', plain, ($false),
% 2.36/2.56      inference('simplify_reflect-', [status(thm)], ['126', '129'])).
% 2.36/2.56  
% 2.36/2.56  % SZS output end Refutation
% 2.36/2.56  
% 2.36/2.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
