%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Jry2QdZn8v

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:55 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  231 (1049 expanded)
%              Number of leaves         :   51 ( 324 expanded)
%              Depth                    :   23
%              Number of atoms          : 2214 (27541 expanded)
%              Number of equality atoms :  146 (1923 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ X9 @ ( k2_funct_1 @ X9 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ X9 @ ( k2_funct_1 @ X9 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

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

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
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

thf('4',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( X54 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_funct_2 @ X55 @ X56 @ X54 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X54 ) ) )
      | ( ( k5_relat_1 @ X55 @ ( k2_funct_1 @ X55 ) )
        = ( k6_partfun1 @ X56 ) )
      | ~ ( v2_funct_1 @ X55 )
      | ( ( k2_relset_1 @ X56 @ X54 @ X55 )
       != X54 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('5',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','8','9','10'])).

thf('12',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 )
        = ( k5_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_funct_2,axiom,(
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

thf('24',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( v2_funct_2 @ X41 @ X43 )
      | ~ ( r2_relset_1 @ X43 @ X43 @ ( k1_partfun1 @ X43 @ X42 @ X42 @ X43 @ X44 @ X41 ) @ ( k6_partfun1 @ X43 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X43 @ X42 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t29_funct_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) @ ( k6_partfun1 @ sk_A ) )
      | ( v2_funct_2 @ sk_D @ sk_A )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) @ ( k6_partfun1 @ sk_A ) )
      | ( v2_funct_2 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('32',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['29','32','33','34','35'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('37',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v2_funct_2 @ X27 @ X26 )
      | ( ( k2_relat_1 @ X27 )
        = X26 )
      | ~ ( v5_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( ( k2_relat_1 @ sk_D )
      = sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('40',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('41',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('43',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('44',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['38','41','44'])).

thf('46',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','45'])).

thf('47',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('49',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
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

thf('52',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('59',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('60',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( X21 = X24 )
      | ~ ( r2_relset_1 @ X22 @ X23 @ X21 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','61'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('63',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('64',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('65',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['48','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ! [E: $i] :
          ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
            & ( v1_funct_2 @ E @ B @ C )
            & ( v1_funct_1 @ E ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ D )
                = B )
              & ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) )
           => ( ( ( v2_funct_1 @ E )
                & ( v2_funct_1 @ D ) )
              | ( ( B != k1_xboole_0 )
                & ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i] :
      ( ( zip_tseitin_1 @ C @ B )
     => ( ( C = k1_xboole_0 )
        & ( B != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [E: $i,D: $i] :
      ( ( zip_tseitin_0 @ E @ D )
     => ( ( v2_funct_1 @ D )
        & ( v2_funct_1 @ E ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
              & ( ( k2_relset_1 @ A @ B @ D )
                = B ) )
           => ( ( zip_tseitin_1 @ C @ B )
              | ( zip_tseitin_0 @ E @ D ) ) ) ) ) )).

thf('69',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( zip_tseitin_0 @ X49 @ X52 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X53 @ X50 @ X50 @ X51 @ X52 @ X49 ) )
      | ( zip_tseitin_1 @ X51 @ X50 )
      | ( ( k2_relset_1 @ X53 @ X50 @ X52 )
       != X50 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X53 @ X50 )
      | ~ ( v1_funct_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf('75',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k5_relat_1 @ X9 @ ( k2_funct_1 @ X9 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( X54 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_funct_2 @ X55 @ X56 @ X54 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X54 ) ) )
      | ( ( k5_relat_1 @ X55 @ ( k2_funct_1 @ X55 ) )
        = ( k6_partfun1 @ X56 ) )
      | ~ ( v2_funct_1 @ X55 )
      | ( ( k2_relset_1 @ X56 @ X54 @ X55 )
       != X54 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('78',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['78','79','80','81','82'])).

thf('84',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['75','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('90',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['87','90','91','92'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('95',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['94'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('96',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X6 ) @ X5 )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('97',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('98',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X6 ) @ X5 )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('100',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('102',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('103',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('104',plain,(
    ! [X4: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X4 ) )
      = X4 ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X25: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('106',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['101','104','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ( v2_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ~ ( v1_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['93','109'])).

thf('111',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['88','89'])).

thf('113',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['87','90','91','92'])).

thf('115',plain,
    ( ~ ( v1_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['110','111','112','113','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['116','121'])).

thf('123',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('126',plain,(
    v1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('128',plain,(
    v1_funct_1 @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    v2_funct_1 @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['115','128'])).

thf('130',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['74','129','130','131','132','133'])).

thf('135',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X47: $i,X48: $i] :
      ( ( X47 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('137',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X45: $i,X46: $i] :
      ( ( v2_funct_1 @ X46 )
      | ~ ( zip_tseitin_0 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('141',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['47','141'])).

thf('143',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['2','142'])).

thf('144',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['39','40'])).

thf('145',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['139','140'])).

thf('147',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['143','144','145','146'])).

thf('148',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X3 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('149',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('150',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X3 ) )
      = X3 ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['147','150'])).

thf('152',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X3 ) )
      = X3 ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('153',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['62','65'])).

thf(t63_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('155',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X10
        = ( k2_funct_1 @ X11 ) )
      | ( ( k5_relat_1 @ X11 @ X10 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) )
      | ( ( k2_relat_1 @ X11 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('156',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('157',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X10
        = ( k2_funct_1 @ X11 ) )
      | ( ( k5_relat_1 @ X11 @ X10 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) )
      | ( ( k2_relat_1 @ X11 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['154','157'])).

thf('159',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['87','90','91','92'])).

thf('160',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X3 ) )
      = X3 ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('161',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X3: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X3 ) )
      = X3 ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('163',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['88','89'])).

thf('165',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('169',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['39','40'])).

thf('174',plain,
    ( ( ( k6_partfun1 @ sk_A )
     != ( k6_partfun1 @ sk_A ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['158','163','164','165','166','171','172','173'])).

thf('175',plain,
    ( ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    sk_B
 != ( k1_relat_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['175','176'])).

thf('178',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['153','177'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Jry2QdZn8v
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:05:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.59/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.80  % Solved by: fo/fo7.sh
% 0.59/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.80  % done 644 iterations in 0.348s
% 0.59/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.80  % SZS output start Refutation
% 0.59/0.80  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.59/0.80  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.59/0.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.80  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.59/0.80  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.80  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.80  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.59/0.80  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.59/0.80  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.59/0.80  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.59/0.80  thf(sk_D_type, type, sk_D: $i).
% 0.59/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.81  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.81  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.81  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.59/0.81  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.59/0.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.81  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.59/0.81  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.59/0.81  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.59/0.81  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.59/0.81  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.81  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.59/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.81  thf(t61_funct_1, axiom,
% 0.59/0.81    (![A:$i]:
% 0.59/0.81     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.81       ( ( v2_funct_1 @ A ) =>
% 0.59/0.81         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.59/0.81             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.59/0.81           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.59/0.81             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.59/0.81  thf('0', plain,
% 0.59/0.81      (![X9 : $i]:
% 0.59/0.81         (~ (v2_funct_1 @ X9)
% 0.59/0.81          | ((k5_relat_1 @ X9 @ (k2_funct_1 @ X9))
% 0.59/0.81              = (k6_relat_1 @ (k1_relat_1 @ X9)))
% 0.59/0.81          | ~ (v1_funct_1 @ X9)
% 0.59/0.81          | ~ (v1_relat_1 @ X9))),
% 0.59/0.81      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.59/0.81  thf(redefinition_k6_partfun1, axiom,
% 0.59/0.81    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.59/0.81  thf('1', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.59/0.81      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.59/0.81  thf('2', plain,
% 0.59/0.81      (![X9 : $i]:
% 0.59/0.81         (~ (v2_funct_1 @ X9)
% 0.59/0.81          | ((k5_relat_1 @ X9 @ (k2_funct_1 @ X9))
% 0.59/0.81              = (k6_partfun1 @ (k1_relat_1 @ X9)))
% 0.59/0.81          | ~ (v1_funct_1 @ X9)
% 0.59/0.81          | ~ (v1_relat_1 @ X9))),
% 0.59/0.81      inference('demod', [status(thm)], ['0', '1'])).
% 0.59/0.81  thf(t36_funct_2, conjecture,
% 0.59/0.81    (![A:$i,B:$i,C:$i]:
% 0.59/0.81     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.59/0.81         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.81       ( ![D:$i]:
% 0.59/0.81         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.59/0.81             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.59/0.81           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.59/0.81               ( r2_relset_1 @
% 0.59/0.81                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.59/0.81                 ( k6_partfun1 @ A ) ) & 
% 0.59/0.81               ( v2_funct_1 @ C ) ) =>
% 0.59/0.81             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.59/0.81               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.59/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.81    (~( ![A:$i,B:$i,C:$i]:
% 0.59/0.81        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.59/0.81            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.81          ( ![D:$i]:
% 0.59/0.81            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.59/0.81                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.59/0.81              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.59/0.81                  ( r2_relset_1 @
% 0.59/0.81                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.59/0.81                    ( k6_partfun1 @ A ) ) & 
% 0.59/0.81                  ( v2_funct_1 @ C ) ) =>
% 0.59/0.81                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.59/0.81                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.59/0.81    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.59/0.81  thf('3', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf(t35_funct_2, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i]:
% 0.59/0.81     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.59/0.81         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.81       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.59/0.81         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.59/0.81           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.59/0.81             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.59/0.81  thf('4', plain,
% 0.59/0.81      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.59/0.81         (((X54) = (k1_xboole_0))
% 0.59/0.81          | ~ (v1_funct_1 @ X55)
% 0.59/0.81          | ~ (v1_funct_2 @ X55 @ X56 @ X54)
% 0.59/0.81          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X54)))
% 0.59/0.81          | ((k5_relat_1 @ X55 @ (k2_funct_1 @ X55)) = (k6_partfun1 @ X56))
% 0.59/0.81          | ~ (v2_funct_1 @ X55)
% 0.59/0.81          | ((k2_relset_1 @ X56 @ X54 @ X55) != (X54)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.59/0.81  thf('5', plain,
% 0.59/0.81      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 0.59/0.81        | ~ (v2_funct_1 @ sk_D)
% 0.59/0.81        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.59/0.81        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.59/0.81        | ~ (v1_funct_1 @ sk_D)
% 0.59/0.81        | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['3', '4'])).
% 0.59/0.81  thf('6', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf(redefinition_k2_relset_1, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i]:
% 0.59/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.81       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.59/0.81  thf('7', plain,
% 0.59/0.81      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.59/0.81         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 0.59/0.81          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.59/0.81      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.59/0.81  thf('8', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.59/0.81      inference('sup-', [status(thm)], ['6', '7'])).
% 0.59/0.81  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('11', plain,
% 0.59/0.81      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.59/0.81        | ~ (v2_funct_1 @ sk_D)
% 0.59/0.81        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.59/0.81        | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.81      inference('demod', [status(thm)], ['5', '8', '9', '10'])).
% 0.59/0.81  thf('12', plain, (((sk_A) != (k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('13', plain,
% 0.59/0.81      ((((k2_relat_1 @ sk_D) != (sk_A))
% 0.59/0.81        | ~ (v2_funct_1 @ sk_D)
% 0.59/0.81        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 0.59/0.81      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.59/0.81  thf('14', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('15', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf(redefinition_k1_partfun1, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.59/0.81     ( ( ( v1_funct_1 @ E ) & 
% 0.59/0.81         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.59/0.81         ( v1_funct_1 @ F ) & 
% 0.59/0.81         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.59/0.81       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.59/0.81  thf('16', plain,
% 0.59/0.81      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.59/0.81         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.59/0.81          | ~ (v1_funct_1 @ X34)
% 0.59/0.81          | ~ (v1_funct_1 @ X37)
% 0.59/0.81          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.59/0.81          | ((k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37)
% 0.59/0.81              = (k5_relat_1 @ X34 @ X37)))),
% 0.59/0.81      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.59/0.81  thf('17', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.81         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.59/0.81            = (k5_relat_1 @ sk_C @ X0))
% 0.59/0.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.59/0.81          | ~ (v1_funct_1 @ X0)
% 0.59/0.81          | ~ (v1_funct_1 @ sk_C))),
% 0.59/0.81      inference('sup-', [status(thm)], ['15', '16'])).
% 0.59/0.81  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('19', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.81         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.59/0.81            = (k5_relat_1 @ sk_C @ X0))
% 0.59/0.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.59/0.81          | ~ (v1_funct_1 @ X0))),
% 0.59/0.81      inference('demod', [status(thm)], ['17', '18'])).
% 0.59/0.81  thf('20', plain,
% 0.59/0.81      ((~ (v1_funct_1 @ sk_D)
% 0.59/0.81        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.59/0.81            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['14', '19'])).
% 0.59/0.81  thf('21', plain, ((v1_funct_1 @ sk_D)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('22', plain,
% 0.59/0.81      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.59/0.81         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.59/0.81      inference('demod', [status(thm)], ['20', '21'])).
% 0.59/0.81  thf('23', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf(t29_funct_2, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i]:
% 0.59/0.81     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.59/0.81         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.81       ( ![D:$i]:
% 0.59/0.81         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.59/0.81             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.59/0.81           ( ( r2_relset_1 @
% 0.59/0.81               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.59/0.81               ( k6_partfun1 @ A ) ) =>
% 0.59/0.81             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.59/0.81  thf('24', plain,
% 0.59/0.81      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.59/0.81         (~ (v1_funct_1 @ X41)
% 0.59/0.81          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 0.59/0.81          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.59/0.81          | (v2_funct_2 @ X41 @ X43)
% 0.59/0.81          | ~ (r2_relset_1 @ X43 @ X43 @ 
% 0.59/0.81               (k1_partfun1 @ X43 @ X42 @ X42 @ X43 @ X44 @ X41) @ 
% 0.59/0.81               (k6_partfun1 @ X43))
% 0.59/0.81          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 0.59/0.81          | ~ (v1_funct_2 @ X44 @ X43 @ X42)
% 0.59/0.81          | ~ (v1_funct_1 @ X44))),
% 0.59/0.81      inference('cnf', [status(esa)], [t29_funct_2])).
% 0.59/0.81  thf('25', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (v1_funct_1 @ X0)
% 0.59/0.81          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_B)
% 0.59/0.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.59/0.81          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.81               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D) @ 
% 0.59/0.81               (k6_partfun1 @ sk_A))
% 0.59/0.81          | (v2_funct_2 @ sk_D @ sk_A)
% 0.59/0.81          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.59/0.81          | ~ (v1_funct_1 @ sk_D))),
% 0.59/0.81      inference('sup-', [status(thm)], ['23', '24'])).
% 0.59/0.81  thf('26', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('27', plain, ((v1_funct_1 @ sk_D)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('28', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (v1_funct_1 @ X0)
% 0.59/0.81          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_B)
% 0.59/0.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.59/0.81          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.81               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D) @ 
% 0.59/0.81               (k6_partfun1 @ sk_A))
% 0.59/0.81          | (v2_funct_2 @ sk_D @ sk_A))),
% 0.59/0.81      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.59/0.81  thf('29', plain,
% 0.59/0.81      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.59/0.81           (k6_partfun1 @ sk_A))
% 0.59/0.81        | (v2_funct_2 @ sk_D @ sk_A)
% 0.59/0.81        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.59/0.81        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.59/0.81        | ~ (v1_funct_1 @ sk_C))),
% 0.59/0.81      inference('sup-', [status(thm)], ['22', '28'])).
% 0.59/0.81  thf('30', plain,
% 0.59/0.81      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.59/0.81        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.59/0.81        (k6_partfun1 @ sk_A))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('31', plain,
% 0.59/0.81      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.59/0.81         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.59/0.81      inference('demod', [status(thm)], ['20', '21'])).
% 0.59/0.81  thf('32', plain,
% 0.59/0.81      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.59/0.81        (k6_partfun1 @ sk_A))),
% 0.59/0.81      inference('demod', [status(thm)], ['30', '31'])).
% 0.59/0.81  thf('33', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('34', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('36', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.59/0.81      inference('demod', [status(thm)], ['29', '32', '33', '34', '35'])).
% 0.59/0.81  thf(d3_funct_2, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.59/0.81       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.59/0.81  thf('37', plain,
% 0.59/0.81      (![X26 : $i, X27 : $i]:
% 0.59/0.81         (~ (v2_funct_2 @ X27 @ X26)
% 0.59/0.81          | ((k2_relat_1 @ X27) = (X26))
% 0.59/0.81          | ~ (v5_relat_1 @ X27 @ X26)
% 0.59/0.81          | ~ (v1_relat_1 @ X27))),
% 0.59/0.81      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.59/0.81  thf('38', plain,
% 0.59/0.81      ((~ (v1_relat_1 @ sk_D)
% 0.59/0.81        | ~ (v5_relat_1 @ sk_D @ sk_A)
% 0.59/0.81        | ((k2_relat_1 @ sk_D) = (sk_A)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['36', '37'])).
% 0.59/0.81  thf('39', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf(cc1_relset_1, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i]:
% 0.59/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.81       ( v1_relat_1 @ C ) ))).
% 0.59/0.81  thf('40', plain,
% 0.59/0.81      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.59/0.81         ((v1_relat_1 @ X12)
% 0.59/0.81          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.59/0.81      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.59/0.81  thf('41', plain, ((v1_relat_1 @ sk_D)),
% 0.59/0.81      inference('sup-', [status(thm)], ['39', '40'])).
% 0.59/0.81  thf('42', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf(cc2_relset_1, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i]:
% 0.59/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.81       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.59/0.81  thf('43', plain,
% 0.59/0.81      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.81         ((v5_relat_1 @ X15 @ X17)
% 0.59/0.81          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.59/0.81      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.59/0.81  thf('44', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.59/0.81      inference('sup-', [status(thm)], ['42', '43'])).
% 0.59/0.81  thf('45', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.59/0.81      inference('demod', [status(thm)], ['38', '41', '44'])).
% 0.59/0.81  thf('46', plain,
% 0.59/0.81      ((((sk_A) != (sk_A))
% 0.59/0.81        | ~ (v2_funct_1 @ sk_D)
% 0.59/0.81        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B)))),
% 0.59/0.81      inference('demod', [status(thm)], ['13', '45'])).
% 0.59/0.81  thf('47', plain,
% 0.59/0.81      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.59/0.81        | ~ (v2_funct_1 @ sk_D))),
% 0.59/0.81      inference('simplify', [status(thm)], ['46'])).
% 0.59/0.81  thf('48', plain,
% 0.59/0.81      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.59/0.81         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.59/0.81      inference('demod', [status(thm)], ['20', '21'])).
% 0.59/0.81  thf('49', plain,
% 0.59/0.81      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.59/0.81        (k6_partfun1 @ sk_A))),
% 0.59/0.81      inference('demod', [status(thm)], ['30', '31'])).
% 0.59/0.81  thf('50', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('51', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf(dt_k1_partfun1, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.59/0.81     ( ( ( v1_funct_1 @ E ) & 
% 0.59/0.81         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.59/0.81         ( v1_funct_1 @ F ) & 
% 0.59/0.81         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.59/0.81       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.59/0.81         ( m1_subset_1 @
% 0.59/0.81           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.59/0.81           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.59/0.81  thf('52', plain,
% 0.59/0.81      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.59/0.81         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.59/0.81          | ~ (v1_funct_1 @ X28)
% 0.59/0.81          | ~ (v1_funct_1 @ X31)
% 0.59/0.81          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.59/0.81          | (m1_subset_1 @ (k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31) @ 
% 0.59/0.81             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X33))))),
% 0.59/0.81      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.59/0.81  thf('53', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.81         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.59/0.81           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.59/0.81          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.59/0.81          | ~ (v1_funct_1 @ X1)
% 0.59/0.81          | ~ (v1_funct_1 @ sk_C))),
% 0.59/0.81      inference('sup-', [status(thm)], ['51', '52'])).
% 0.59/0.81  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('55', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.81         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.59/0.81           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.59/0.81          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.59/0.81          | ~ (v1_funct_1 @ X1))),
% 0.59/0.81      inference('demod', [status(thm)], ['53', '54'])).
% 0.59/0.81  thf('56', plain,
% 0.59/0.81      ((~ (v1_funct_1 @ sk_D)
% 0.59/0.81        | (m1_subset_1 @ 
% 0.59/0.81           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.59/0.81           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['50', '55'])).
% 0.59/0.81  thf('57', plain, ((v1_funct_1 @ sk_D)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('58', plain,
% 0.59/0.81      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.59/0.81         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.59/0.81      inference('demod', [status(thm)], ['20', '21'])).
% 0.59/0.81  thf('59', plain,
% 0.59/0.81      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.59/0.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.59/0.81      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.59/0.81  thf(redefinition_r2_relset_1, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.81     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.59/0.81         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.81       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.59/0.81  thf('60', plain,
% 0.59/0.81      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.59/0.81         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.59/0.81          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.59/0.81          | ((X21) = (X24))
% 0.59/0.81          | ~ (r2_relset_1 @ X22 @ X23 @ X21 @ X24))),
% 0.59/0.81      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.59/0.81  thf('61', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.59/0.81          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.59/0.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['59', '60'])).
% 0.59/0.81  thf('62', plain,
% 0.59/0.81      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.59/0.81           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.59/0.81        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['49', '61'])).
% 0.59/0.81  thf(t29_relset_1, axiom,
% 0.59/0.81    (![A:$i]:
% 0.59/0.81     ( m1_subset_1 @
% 0.59/0.81       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.59/0.81  thf('63', plain,
% 0.59/0.81      (![X25 : $i]:
% 0.59/0.81         (m1_subset_1 @ (k6_relat_1 @ X25) @ 
% 0.59/0.81          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.59/0.81  thf('64', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.59/0.81      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.59/0.81  thf('65', plain,
% 0.59/0.81      (![X25 : $i]:
% 0.59/0.81         (m1_subset_1 @ (k6_partfun1 @ X25) @ 
% 0.59/0.81          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 0.59/0.81      inference('demod', [status(thm)], ['63', '64'])).
% 0.59/0.81  thf('66', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.59/0.81      inference('demod', [status(thm)], ['62', '65'])).
% 0.59/0.81  thf('67', plain,
% 0.59/0.81      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.59/0.81         = (k6_partfun1 @ sk_A))),
% 0.59/0.81      inference('demod', [status(thm)], ['48', '66'])).
% 0.59/0.81  thf('68', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf(t30_funct_2, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.81     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.59/0.81         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.59/0.81       ( ![E:$i]:
% 0.59/0.81         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 0.59/0.81             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 0.59/0.81           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 0.59/0.81               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 0.59/0.81             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 0.59/0.81               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 0.59/0.81  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.59/0.81  thf(zf_stmt_2, axiom,
% 0.59/0.81    (![C:$i,B:$i]:
% 0.59/0.81     ( ( zip_tseitin_1 @ C @ B ) =>
% 0.59/0.81       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 0.59/0.81  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.59/0.81  thf(zf_stmt_4, axiom,
% 0.59/0.81    (![E:$i,D:$i]:
% 0.59/0.81     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 0.59/0.81  thf(zf_stmt_5, axiom,
% 0.59/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.81     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.59/0.81         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.81       ( ![E:$i]:
% 0.59/0.81         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.59/0.81             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.59/0.81           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 0.59/0.81               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 0.59/0.81             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 0.59/0.81  thf('69', plain,
% 0.59/0.81      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 0.59/0.81         (~ (v1_funct_1 @ X49)
% 0.59/0.81          | ~ (v1_funct_2 @ X49 @ X50 @ X51)
% 0.59/0.81          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 0.59/0.81          | (zip_tseitin_0 @ X49 @ X52)
% 0.59/0.81          | ~ (v2_funct_1 @ (k1_partfun1 @ X53 @ X50 @ X50 @ X51 @ X52 @ X49))
% 0.59/0.81          | (zip_tseitin_1 @ X51 @ X50)
% 0.59/0.81          | ((k2_relset_1 @ X53 @ X50 @ X52) != (X50))
% 0.59/0.81          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X50)))
% 0.59/0.81          | ~ (v1_funct_2 @ X52 @ X53 @ X50)
% 0.59/0.81          | ~ (v1_funct_1 @ X52))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.59/0.81  thf('70', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (~ (v1_funct_1 @ X0)
% 0.59/0.81          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.59/0.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.59/0.81          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.59/0.81          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.59/0.81          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.59/0.81          | (zip_tseitin_0 @ sk_D @ X0)
% 0.59/0.81          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.59/0.81          | ~ (v1_funct_1 @ sk_D))),
% 0.59/0.81      inference('sup-', [status(thm)], ['68', '69'])).
% 0.59/0.81  thf('71', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('72', plain, ((v1_funct_1 @ sk_D)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('73', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]:
% 0.59/0.81         (~ (v1_funct_1 @ X0)
% 0.59/0.81          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.59/0.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.59/0.81          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 0.59/0.81          | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.59/0.81          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.59/0.81          | (zip_tseitin_0 @ sk_D @ X0))),
% 0.59/0.81      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.59/0.81  thf('74', plain,
% 0.59/0.81      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.59/0.81        | (zip_tseitin_0 @ sk_D @ sk_C)
% 0.59/0.81        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.59/0.81        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.59/0.81        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.59/0.81        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.59/0.81        | ~ (v1_funct_1 @ sk_C))),
% 0.59/0.81      inference('sup-', [status(thm)], ['67', '73'])).
% 0.59/0.81  thf('75', plain,
% 0.59/0.81      (![X9 : $i]:
% 0.59/0.81         (~ (v2_funct_1 @ X9)
% 0.59/0.81          | ((k5_relat_1 @ X9 @ (k2_funct_1 @ X9))
% 0.59/0.81              = (k6_partfun1 @ (k1_relat_1 @ X9)))
% 0.59/0.81          | ~ (v1_funct_1 @ X9)
% 0.59/0.81          | ~ (v1_relat_1 @ X9))),
% 0.59/0.81      inference('demod', [status(thm)], ['0', '1'])).
% 0.59/0.81  thf('76', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('77', plain,
% 0.59/0.81      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.59/0.81         (((X54) = (k1_xboole_0))
% 0.59/0.81          | ~ (v1_funct_1 @ X55)
% 0.59/0.81          | ~ (v1_funct_2 @ X55 @ X56 @ X54)
% 0.59/0.81          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X54)))
% 0.59/0.81          | ((k5_relat_1 @ X55 @ (k2_funct_1 @ X55)) = (k6_partfun1 @ X56))
% 0.59/0.81          | ~ (v2_funct_1 @ X55)
% 0.59/0.81          | ((k2_relset_1 @ X56 @ X54 @ X55) != (X54)))),
% 0.59/0.81      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.59/0.81  thf('78', plain,
% 0.59/0.81      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.59/0.81        | ~ (v2_funct_1 @ sk_C)
% 0.59/0.81        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.59/0.81        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.59/0.81        | ~ (v1_funct_1 @ sk_C)
% 0.59/0.81        | ((sk_B) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['76', '77'])).
% 0.59/0.81  thf('79', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('80', plain, ((v2_funct_1 @ sk_C)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('81', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('82', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('83', plain,
% 0.59/0.81      ((((sk_B) != (sk_B))
% 0.59/0.81        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.59/0.81        | ((sk_B) = (k1_xboole_0)))),
% 0.59/0.81      inference('demod', [status(thm)], ['78', '79', '80', '81', '82'])).
% 0.59/0.81  thf('84', plain,
% 0.59/0.81      ((((sk_B) = (k1_xboole_0))
% 0.59/0.81        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 0.59/0.81      inference('simplify', [status(thm)], ['83'])).
% 0.59/0.81  thf('85', plain, (((sk_B) != (k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('86', plain,
% 0.59/0.81      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.59/0.81      inference('simplify_reflect-', [status(thm)], ['84', '85'])).
% 0.59/0.81  thf('87', plain,
% 0.59/0.81      ((((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 0.59/0.81        | ~ (v1_relat_1 @ sk_C)
% 0.59/0.81        | ~ (v1_funct_1 @ sk_C)
% 0.59/0.81        | ~ (v2_funct_1 @ sk_C))),
% 0.59/0.81      inference('sup+', [status(thm)], ['75', '86'])).
% 0.59/0.81  thf('88', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('89', plain,
% 0.59/0.81      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.59/0.81         ((v1_relat_1 @ X12)
% 0.59/0.81          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.59/0.81      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.59/0.81  thf('90', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.81      inference('sup-', [status(thm)], ['88', '89'])).
% 0.59/0.81  thf('91', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('92', plain, ((v2_funct_1 @ sk_C)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('93', plain,
% 0.59/0.81      (((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.59/0.81      inference('demod', [status(thm)], ['87', '90', '91', '92'])).
% 0.59/0.81  thf(d10_xboole_0, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.81  thf('94', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.59/0.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.81  thf('95', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.59/0.81      inference('simplify', [status(thm)], ['94'])).
% 0.59/0.81  thf(t77_relat_1, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( v1_relat_1 @ B ) =>
% 0.59/0.81       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.59/0.81         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.59/0.81  thf('96', plain,
% 0.59/0.81      (![X5 : $i, X6 : $i]:
% 0.59/0.81         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.59/0.81          | ((k5_relat_1 @ (k6_relat_1 @ X6) @ X5) = (X5))
% 0.59/0.81          | ~ (v1_relat_1 @ X5))),
% 0.59/0.81      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.59/0.81  thf('97', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.59/0.81      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.59/0.81  thf('98', plain,
% 0.59/0.81      (![X5 : $i, X6 : $i]:
% 0.59/0.81         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.59/0.81          | ((k5_relat_1 @ (k6_partfun1 @ X6) @ X5) = (X5))
% 0.59/0.81          | ~ (v1_relat_1 @ X5))),
% 0.59/0.81      inference('demod', [status(thm)], ['96', '97'])).
% 0.59/0.81  thf('99', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (v1_relat_1 @ X0)
% 0.59/0.81          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['95', '98'])).
% 0.59/0.81  thf(t48_funct_1, axiom,
% 0.59/0.81    (![A:$i]:
% 0.59/0.81     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.81       ( ![B:$i]:
% 0.59/0.81         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.81           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.59/0.81               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.59/0.81             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.59/0.81  thf('100', plain,
% 0.59/0.81      (![X7 : $i, X8 : $i]:
% 0.59/0.81         (~ (v1_relat_1 @ X7)
% 0.59/0.81          | ~ (v1_funct_1 @ X7)
% 0.59/0.81          | (v2_funct_1 @ X7)
% 0.59/0.81          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 0.59/0.81          | ~ (v2_funct_1 @ (k5_relat_1 @ X7 @ X8))
% 0.59/0.81          | ~ (v1_funct_1 @ X8)
% 0.59/0.81          | ~ (v1_relat_1 @ X8))),
% 0.59/0.81      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.59/0.81  thf('101', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (v2_funct_1 @ X0)
% 0.59/0.81          | ~ (v1_relat_1 @ X0)
% 0.59/0.81          | ~ (v1_relat_1 @ X0)
% 0.59/0.81          | ~ (v1_funct_1 @ X0)
% 0.59/0.81          | ((k2_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.59/0.81              != (k1_relat_1 @ X0))
% 0.59/0.81          | (v2_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.59/0.81          | ~ (v1_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.59/0.81          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['99', '100'])).
% 0.59/0.81  thf(t71_relat_1, axiom,
% 0.59/0.81    (![A:$i]:
% 0.59/0.81     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.59/0.81       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.59/0.81  thf('102', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X4)) = (X4))),
% 0.59/0.81      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.59/0.81  thf('103', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.59/0.81      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.59/0.81  thf('104', plain, (![X4 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X4)) = (X4))),
% 0.59/0.81      inference('demod', [status(thm)], ['102', '103'])).
% 0.59/0.81  thf('105', plain,
% 0.59/0.81      (![X25 : $i]:
% 0.59/0.81         (m1_subset_1 @ (k6_partfun1 @ X25) @ 
% 0.59/0.81          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25)))),
% 0.59/0.81      inference('demod', [status(thm)], ['63', '64'])).
% 0.59/0.81  thf('106', plain,
% 0.59/0.81      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.59/0.81         ((v1_relat_1 @ X12)
% 0.59/0.81          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.59/0.81      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.59/0.81  thf('107', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 0.59/0.81      inference('sup-', [status(thm)], ['105', '106'])).
% 0.59/0.81  thf('108', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (v2_funct_1 @ X0)
% 0.59/0.81          | ~ (v1_relat_1 @ X0)
% 0.59/0.81          | ~ (v1_relat_1 @ X0)
% 0.59/0.81          | ~ (v1_funct_1 @ X0)
% 0.59/0.81          | ((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.59/0.81          | (v2_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.59/0.81          | ~ (v1_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ X0))))),
% 0.59/0.81      inference('demod', [status(thm)], ['101', '104', '107'])).
% 0.59/0.81  thf('109', plain,
% 0.59/0.81      (![X0 : $i]:
% 0.59/0.81         (~ (v1_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.59/0.81          | (v2_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.59/0.81          | ~ (v1_funct_1 @ X0)
% 0.59/0.81          | ~ (v1_relat_1 @ X0)
% 0.59/0.81          | ~ (v2_funct_1 @ X0))),
% 0.59/0.81      inference('simplify', [status(thm)], ['108'])).
% 0.59/0.81  thf('110', plain,
% 0.59/0.81      ((~ (v1_funct_1 @ (k6_partfun1 @ sk_A))
% 0.59/0.81        | ~ (v2_funct_1 @ sk_C)
% 0.59/0.81        | ~ (v1_relat_1 @ sk_C)
% 0.59/0.81        | ~ (v1_funct_1 @ sk_C)
% 0.59/0.81        | (v2_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['93', '109'])).
% 0.59/0.81  thf('111', plain, ((v2_funct_1 @ sk_C)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('112', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.81      inference('sup-', [status(thm)], ['88', '89'])).
% 0.59/0.81  thf('113', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('114', plain,
% 0.59/0.81      (((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.59/0.81      inference('demod', [status(thm)], ['87', '90', '91', '92'])).
% 0.59/0.81  thf('115', plain,
% 0.59/0.81      ((~ (v1_funct_1 @ (k6_partfun1 @ sk_A))
% 0.59/0.81        | (v2_funct_1 @ (k6_partfun1 @ sk_A)))),
% 0.59/0.81      inference('demod', [status(thm)], ['110', '111', '112', '113', '114'])).
% 0.59/0.81  thf('116', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('117', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('118', plain,
% 0.59/0.81      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.59/0.81         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.59/0.81          | ~ (v1_funct_1 @ X28)
% 0.59/0.81          | ~ (v1_funct_1 @ X31)
% 0.59/0.81          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.59/0.81          | (v1_funct_1 @ (k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31)))),
% 0.59/0.81      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.59/0.81  thf('119', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.81         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0))
% 0.59/0.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.59/0.81          | ~ (v1_funct_1 @ X0)
% 0.59/0.81          | ~ (v1_funct_1 @ sk_C))),
% 0.59/0.81      inference('sup-', [status(thm)], ['117', '118'])).
% 0.59/0.81  thf('120', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('121', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.81         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0))
% 0.59/0.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.59/0.81          | ~ (v1_funct_1 @ X0))),
% 0.59/0.81      inference('demod', [status(thm)], ['119', '120'])).
% 0.59/0.81  thf('122', plain,
% 0.59/0.81      ((~ (v1_funct_1 @ sk_D)
% 0.59/0.81        | (v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['116', '121'])).
% 0.59/0.81  thf('123', plain, ((v1_funct_1 @ sk_D)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('124', plain,
% 0.59/0.81      ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D))),
% 0.59/0.81      inference('demod', [status(thm)], ['122', '123'])).
% 0.59/0.81  thf('125', plain,
% 0.59/0.81      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.59/0.81         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.59/0.81      inference('demod', [status(thm)], ['20', '21'])).
% 0.59/0.81  thf('126', plain, ((v1_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 0.59/0.81      inference('demod', [status(thm)], ['124', '125'])).
% 0.59/0.81  thf('127', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.59/0.81      inference('demod', [status(thm)], ['62', '65'])).
% 0.59/0.81  thf('128', plain, ((v1_funct_1 @ (k6_partfun1 @ sk_A))),
% 0.59/0.81      inference('demod', [status(thm)], ['126', '127'])).
% 0.59/0.81  thf('129', plain, ((v2_funct_1 @ (k6_partfun1 @ sk_A))),
% 0.59/0.81      inference('demod', [status(thm)], ['115', '128'])).
% 0.59/0.81  thf('130', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('131', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('132', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('133', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('134', plain,
% 0.59/0.81      (((zip_tseitin_0 @ sk_D @ sk_C)
% 0.59/0.81        | (zip_tseitin_1 @ sk_A @ sk_B)
% 0.59/0.81        | ((sk_B) != (sk_B)))),
% 0.59/0.81      inference('demod', [status(thm)],
% 0.59/0.81                ['74', '129', '130', '131', '132', '133'])).
% 0.59/0.81  thf('135', plain,
% 0.59/0.81      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 0.59/0.81      inference('simplify', [status(thm)], ['134'])).
% 0.59/0.81  thf('136', plain,
% 0.59/0.81      (![X47 : $i, X48 : $i]:
% 0.59/0.81         (((X47) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X47 @ X48))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.59/0.81  thf('137', plain,
% 0.59/0.81      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['135', '136'])).
% 0.59/0.81  thf('138', plain, (((sk_A) != (k1_xboole_0))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('139', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 0.59/0.81      inference('simplify_reflect-', [status(thm)], ['137', '138'])).
% 0.59/0.81  thf('140', plain,
% 0.59/0.81      (![X45 : $i, X46 : $i]:
% 0.59/0.81         ((v2_funct_1 @ X46) | ~ (zip_tseitin_0 @ X46 @ X45))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.59/0.81  thf('141', plain, ((v2_funct_1 @ sk_D)),
% 0.59/0.81      inference('sup-', [status(thm)], ['139', '140'])).
% 0.59/0.81  thf('142', plain,
% 0.59/0.81      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.59/0.81      inference('demod', [status(thm)], ['47', '141'])).
% 0.59/0.81  thf('143', plain,
% 0.59/0.81      ((((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))
% 0.59/0.81        | ~ (v1_relat_1 @ sk_D)
% 0.59/0.81        | ~ (v1_funct_1 @ sk_D)
% 0.59/0.81        | ~ (v2_funct_1 @ sk_D))),
% 0.59/0.81      inference('sup+', [status(thm)], ['2', '142'])).
% 0.59/0.81  thf('144', plain, ((v1_relat_1 @ sk_D)),
% 0.59/0.81      inference('sup-', [status(thm)], ['39', '40'])).
% 0.59/0.81  thf('145', plain, ((v1_funct_1 @ sk_D)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('146', plain, ((v2_funct_1 @ sk_D)),
% 0.59/0.81      inference('sup-', [status(thm)], ['139', '140'])).
% 0.59/0.81  thf('147', plain,
% 0.59/0.81      (((k6_partfun1 @ (k1_relat_1 @ sk_D)) = (k6_partfun1 @ sk_B))),
% 0.59/0.81      inference('demod', [status(thm)], ['143', '144', '145', '146'])).
% 0.59/0.81  thf('148', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X3)) = (X3))),
% 0.59/0.81      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.59/0.81  thf('149', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.59/0.81      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.59/0.81  thf('150', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X3)) = (X3))),
% 0.59/0.81      inference('demod', [status(thm)], ['148', '149'])).
% 0.59/0.81  thf('151', plain,
% 0.59/0.81      (((k1_relat_1 @ (k6_partfun1 @ sk_B)) = (k1_relat_1 @ sk_D))),
% 0.59/0.81      inference('sup+', [status(thm)], ['147', '150'])).
% 0.59/0.81  thf('152', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X3)) = (X3))),
% 0.59/0.81      inference('demod', [status(thm)], ['148', '149'])).
% 0.59/0.81  thf('153', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.59/0.81      inference('demod', [status(thm)], ['151', '152'])).
% 0.59/0.81  thf('154', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.59/0.81      inference('demod', [status(thm)], ['62', '65'])).
% 0.59/0.81  thf(t63_funct_1, axiom,
% 0.59/0.81    (![A:$i]:
% 0.59/0.81     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.59/0.81       ( ![B:$i]:
% 0.59/0.81         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.81           ( ( ( v2_funct_1 @ A ) & 
% 0.59/0.81               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.59/0.81               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.59/0.81             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.59/0.81  thf('155', plain,
% 0.59/0.81      (![X10 : $i, X11 : $i]:
% 0.59/0.81         (~ (v1_relat_1 @ X10)
% 0.59/0.81          | ~ (v1_funct_1 @ X10)
% 0.59/0.81          | ((X10) = (k2_funct_1 @ X11))
% 0.59/0.81          | ((k5_relat_1 @ X11 @ X10) != (k6_relat_1 @ (k1_relat_1 @ X11)))
% 0.59/0.81          | ((k2_relat_1 @ X11) != (k1_relat_1 @ X10))
% 0.59/0.81          | ~ (v2_funct_1 @ X11)
% 0.59/0.81          | ~ (v1_funct_1 @ X11)
% 0.59/0.81          | ~ (v1_relat_1 @ X11))),
% 0.59/0.81      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.59/0.81  thf('156', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 0.59/0.81      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.59/0.81  thf('157', plain,
% 0.59/0.81      (![X10 : $i, X11 : $i]:
% 0.59/0.81         (~ (v1_relat_1 @ X10)
% 0.59/0.81          | ~ (v1_funct_1 @ X10)
% 0.59/0.81          | ((X10) = (k2_funct_1 @ X11))
% 0.59/0.81          | ((k5_relat_1 @ X11 @ X10) != (k6_partfun1 @ (k1_relat_1 @ X11)))
% 0.59/0.81          | ((k2_relat_1 @ X11) != (k1_relat_1 @ X10))
% 0.59/0.81          | ~ (v2_funct_1 @ X11)
% 0.59/0.81          | ~ (v1_funct_1 @ X11)
% 0.59/0.81          | ~ (v1_relat_1 @ X11))),
% 0.59/0.81      inference('demod', [status(thm)], ['155', '156'])).
% 0.59/0.81  thf('158', plain,
% 0.59/0.81      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 0.59/0.81        | ~ (v1_relat_1 @ sk_C)
% 0.59/0.81        | ~ (v1_funct_1 @ sk_C)
% 0.59/0.81        | ~ (v2_funct_1 @ sk_C)
% 0.59/0.81        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.59/0.81        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.59/0.81        | ~ (v1_funct_1 @ sk_D)
% 0.59/0.81        | ~ (v1_relat_1 @ sk_D))),
% 0.59/0.81      inference('sup-', [status(thm)], ['154', '157'])).
% 0.59/0.81  thf('159', plain,
% 0.59/0.81      (((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 0.59/0.81      inference('demod', [status(thm)], ['87', '90', '91', '92'])).
% 0.59/0.81  thf('160', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X3)) = (X3))),
% 0.59/0.81      inference('demod', [status(thm)], ['148', '149'])).
% 0.59/0.81  thf('161', plain,
% 0.59/0.81      (((k1_relat_1 @ (k6_partfun1 @ sk_A)) = (k1_relat_1 @ sk_C))),
% 0.59/0.81      inference('sup+', [status(thm)], ['159', '160'])).
% 0.59/0.81  thf('162', plain, (![X3 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X3)) = (X3))),
% 0.59/0.81      inference('demod', [status(thm)], ['148', '149'])).
% 0.59/0.81  thf('163', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.59/0.81      inference('demod', [status(thm)], ['161', '162'])).
% 0.59/0.81  thf('164', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.81      inference('sup-', [status(thm)], ['88', '89'])).
% 0.59/0.81  thf('165', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('166', plain, ((v2_funct_1 @ sk_C)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('167', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('168', plain,
% 0.59/0.81      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.59/0.81         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 0.59/0.81          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.59/0.81      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.59/0.81  thf('169', plain,
% 0.59/0.81      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.59/0.81      inference('sup-', [status(thm)], ['167', '168'])).
% 0.59/0.81  thf('170', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('171', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.59/0.81      inference('sup+', [status(thm)], ['169', '170'])).
% 0.59/0.81  thf('172', plain, ((v1_funct_1 @ sk_D)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('173', plain, ((v1_relat_1 @ sk_D)),
% 0.59/0.81      inference('sup-', [status(thm)], ['39', '40'])).
% 0.59/0.81  thf('174', plain,
% 0.59/0.81      ((((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 0.59/0.81        | ((sk_B) != (k1_relat_1 @ sk_D))
% 0.59/0.81        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.59/0.81      inference('demod', [status(thm)],
% 0.59/0.81                ['158', '163', '164', '165', '166', '171', '172', '173'])).
% 0.59/0.81  thf('175', plain,
% 0.59/0.81      ((((sk_D) = (k2_funct_1 @ sk_C)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 0.59/0.81      inference('simplify', [status(thm)], ['174'])).
% 0.59/0.81  thf('176', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('177', plain, (((sk_B) != (k1_relat_1 @ sk_D))),
% 0.59/0.81      inference('simplify_reflect-', [status(thm)], ['175', '176'])).
% 0.59/0.81  thf('178', plain, ($false),
% 0.59/0.81      inference('simplify_reflect-', [status(thm)], ['153', '177'])).
% 0.59/0.81  
% 0.59/0.81  % SZS output end Refutation
% 0.59/0.81  
% 0.59/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
