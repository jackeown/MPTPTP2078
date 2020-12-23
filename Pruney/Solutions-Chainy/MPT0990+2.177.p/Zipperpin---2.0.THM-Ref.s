%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Av0cvIlAbv

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:25 EST 2020

% Result     : Theorem 2.72s
% Output     : Refutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :  241 (1079 expanded)
%              Number of leaves         :   52 ( 343 expanded)
%              Depth                    :   27
%              Number of atoms          : 2361 (26549 expanded)
%              Number of equality atoms :  165 (1753 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf('1',plain,(
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

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( X54 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_funct_2 @ X55 @ X56 @ X54 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X54 ) ) )
      | ( ( k5_relat_1 @ X55 @ ( k2_funct_1 @ X55 ) )
        = ( k6_relat_1 @ X56 ) )
      | ~ ( v2_funct_1 @ X55 )
      | ( ( k2_relset_1 @ X56 @ X54 @ X55 )
       != X54 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('7',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','7','8','9'])).

thf('11',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k2_relat_1 @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('25',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( X22 = X25 )
      | ~ ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','26'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('28',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('29',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
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

thf('33',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( r2_relset_1 @ X42 @ X42 @ ( k1_partfun1 @ X42 @ X43 @ X43 @ X42 @ X41 @ X44 ) @ ( k6_partfun1 @ X42 ) )
      | ( ( k2_relset_1 @ X43 @ X42 @ X44 )
        = X42 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X43 @ X42 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('34',plain,(
    ! [X40: $i] :
      ( ( k6_partfun1 @ X40 )
      = ( k6_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('35',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( r2_relset_1 @ X42 @ X42 @ ( k1_partfun1 @ X42 @ X43 @ X43 @ X42 @ X41 @ X44 ) @ ( k6_relat_1 @ X42 ) )
      | ( ( k2_relset_1 @ X43 @ X42 @ X44 )
        = X42 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X43 @ X42 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','39'])).

thf('41',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('42',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 )
      | ( X22 != X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('43',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_relset_1 @ X23 @ X24 @ X25 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('46',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['40','44','45','46','47','48'])).

thf('50',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','49'])).

thf('51',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('53',plain,(
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

thf('54',plain,(
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

thf('55',plain,(
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
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','58'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('60',plain,(
    ! [X15: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('61',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['59','60','61','62','63','64'])).

thf('66',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X47: $i,X48: $i] :
      ( ( X47 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('68',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X45: $i,X46: $i] :
      ( ( v2_funct_1 @ X46 )
      | ~ ( zip_tseitin_0 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('72',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['51','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
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

thf('76',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 )
        = ( k5_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('83',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf(t64_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) )
              & ( ( k5_relat_1 @ B @ A )
                = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('84',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( X17
        = ( k2_funct_1 @ X18 ) )
      | ( ( k5_relat_1 @ X17 @ X18 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X18 ) ) )
      | ( ( k2_relat_1 @ X17 )
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v2_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('85',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['40','44','45','46','47','48'])).

thf('87',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('88',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('89',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('90',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('91',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('95',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('101',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('103',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['85','86','91','92','97','98','103'])).

thf('105',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['70','71'])).

thf('107',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('108',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k1_relat_1 @ X16 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('109',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['51','72'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('110',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('111',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('113',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('114',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('115',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ X16 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('117',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X10 ) @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ( ( k2_relat_1 @ ( k6_relat_1 @ sk_B ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['109','122'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('124',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('125',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['89','90'])).

thf('126',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['70','71'])).

thf('128',plain,
    ( sk_B
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['123','124','125','126','127'])).

thf('129',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['108','128'])).

thf('130',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['89','90'])).

thf('131',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['70','71'])).

thf('133',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['129','130','131','132'])).

thf('134',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['107','133'])).

thf('135',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ( k5_relat_1 @ sk_D @ sk_C )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['73','135'])).

thf('137',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( X17
        = ( k2_funct_1 @ X18 ) )
      | ( ( k5_relat_1 @ X17 @ X18 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X18 ) ) )
      | ( ( k2_relat_1 @ X17 )
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v2_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('138',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_D )
     != ( k1_relat_1 @ sk_C ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['95','96'])).

thf('140',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['101','102'])).

thf('141',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['40','44','45','46','47','48'])).

thf('144',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k1_relat_1 @ X16 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('145',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('146',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['95','96'])).

thf('147',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ X16 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('148',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['95','96'])).

thf('149',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X9 @ X10 ) )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X10 ) @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) )
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['101','102'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ X0 ) ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['147','152'])).

thf('154',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['146','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('156',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['101','102'])).

thf('159',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['154','155','156','157','158'])).

thf('160',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['145','159'])).

thf('161',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['101','102'])).

thf('162',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['160','161','162'])).

thf('164',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ( X54 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_funct_2 @ X55 @ X56 @ X54 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X54 ) ) )
      | ( ( k5_relat_1 @ X55 @ ( k2_funct_1 @ X55 ) )
        = ( k6_relat_1 @ X56 ) )
      | ~ ( v2_funct_1 @ X55 )
      | ( ( k2_relset_1 @ X56 @ X54 @ X55 )
       != X54 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('166',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['166','167','168','169','170'])).

thf('172',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X12: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('176',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['163','174','175'])).

thf('177',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['144','176'])).

thf('178',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['101','102'])).

thf('179',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['177','178','179','180'])).

thf('182',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['89','90'])).

thf('184',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ sk_B ) )
    | ( sk_A != sk_A )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['138','139','140','141','142','143','181','182','183'])).

thf('185',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['185','186'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Av0cvIlAbv
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.72/2.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.72/2.98  % Solved by: fo/fo7.sh
% 2.72/2.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.72/2.98  % done 1720 iterations in 2.525s
% 2.72/2.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.72/2.98  % SZS output start Refutation
% 2.72/2.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.72/2.98  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.72/2.98  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.72/2.98  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.72/2.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.72/2.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.72/2.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.72/2.98  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.72/2.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.72/2.98  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 2.72/2.98  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 2.72/2.98  thf(sk_B_type, type, sk_B: $i).
% 2.72/2.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.72/2.98  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.72/2.98  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.72/2.98  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.72/2.98  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.72/2.98  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.72/2.98  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.72/2.98  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.72/2.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.72/2.98  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.72/2.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.72/2.98  thf(sk_A_type, type, sk_A: $i).
% 2.72/2.98  thf(sk_D_type, type, sk_D: $i).
% 2.72/2.98  thf(sk_C_type, type, sk_C: $i).
% 2.72/2.98  thf(t36_funct_2, conjecture,
% 2.72/2.98    (![A:$i,B:$i,C:$i]:
% 2.72/2.98     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.72/2.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.72/2.98       ( ![D:$i]:
% 2.72/2.98         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.72/2.98             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.72/2.98           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.72/2.98               ( r2_relset_1 @
% 2.72/2.98                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.72/2.98                 ( k6_partfun1 @ A ) ) & 
% 2.72/2.98               ( v2_funct_1 @ C ) ) =>
% 2.72/2.98             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.72/2.98               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 2.72/2.98  thf(zf_stmt_0, negated_conjecture,
% 2.72/2.98    (~( ![A:$i,B:$i,C:$i]:
% 2.72/2.98        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.72/2.98            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.72/2.98          ( ![D:$i]:
% 2.72/2.98            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.72/2.98                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.72/2.98              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 2.72/2.98                  ( r2_relset_1 @
% 2.72/2.98                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.72/2.98                    ( k6_partfun1 @ A ) ) & 
% 2.72/2.98                  ( v2_funct_1 @ C ) ) =>
% 2.72/2.98                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.72/2.98                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 2.72/2.98    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 2.72/2.98  thf('0', plain,
% 2.72/2.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf(t35_funct_2, axiom,
% 2.72/2.98    (![A:$i,B:$i,C:$i]:
% 2.72/2.98     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.72/2.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.72/2.98       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 2.72/2.98         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.72/2.98           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 2.72/2.98             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 2.72/2.98  thf('1', plain,
% 2.72/2.98      (![X54 : $i, X55 : $i, X56 : $i]:
% 2.72/2.98         (((X54) = (k1_xboole_0))
% 2.72/2.98          | ~ (v1_funct_1 @ X55)
% 2.72/2.98          | ~ (v1_funct_2 @ X55 @ X56 @ X54)
% 2.72/2.98          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X54)))
% 2.72/2.98          | ((k5_relat_1 @ X55 @ (k2_funct_1 @ X55)) = (k6_partfun1 @ X56))
% 2.72/2.98          | ~ (v2_funct_1 @ X55)
% 2.72/2.98          | ((k2_relset_1 @ X56 @ X54 @ X55) != (X54)))),
% 2.72/2.98      inference('cnf', [status(esa)], [t35_funct_2])).
% 2.72/2.98  thf(redefinition_k6_partfun1, axiom,
% 2.72/2.98    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.72/2.98  thf('2', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 2.72/2.98      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.72/2.98  thf('3', plain,
% 2.72/2.98      (![X54 : $i, X55 : $i, X56 : $i]:
% 2.72/2.98         (((X54) = (k1_xboole_0))
% 2.72/2.98          | ~ (v1_funct_1 @ X55)
% 2.72/2.98          | ~ (v1_funct_2 @ X55 @ X56 @ X54)
% 2.72/2.98          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X54)))
% 2.72/2.98          | ((k5_relat_1 @ X55 @ (k2_funct_1 @ X55)) = (k6_relat_1 @ X56))
% 2.72/2.98          | ~ (v2_funct_1 @ X55)
% 2.72/2.98          | ((k2_relset_1 @ X56 @ X54 @ X55) != (X54)))),
% 2.72/2.98      inference('demod', [status(thm)], ['1', '2'])).
% 2.72/2.98  thf('4', plain,
% 2.72/2.98      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 2.72/2.98        | ~ (v2_funct_1 @ sk_D)
% 2.72/2.98        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 2.72/2.98        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.72/2.98        | ~ (v1_funct_1 @ sk_D)
% 2.72/2.98        | ((sk_A) = (k1_xboole_0)))),
% 2.72/2.98      inference('sup-', [status(thm)], ['0', '3'])).
% 2.72/2.98  thf('5', plain,
% 2.72/2.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf(redefinition_k2_relset_1, axiom,
% 2.72/2.98    (![A:$i,B:$i,C:$i]:
% 2.72/2.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.72/2.98       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.72/2.98  thf('6', plain,
% 2.72/2.98      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.72/2.98         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 2.72/2.98          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 2.72/2.98      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.72/2.98  thf('7', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.72/2.98      inference('sup-', [status(thm)], ['5', '6'])).
% 2.72/2.98  thf('8', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('9', plain, ((v1_funct_1 @ sk_D)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('10', plain,
% 2.72/2.98      ((((k2_relat_1 @ sk_D) != (sk_A))
% 2.72/2.98        | ~ (v2_funct_1 @ sk_D)
% 2.72/2.98        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 2.72/2.98        | ((sk_A) = (k1_xboole_0)))),
% 2.72/2.98      inference('demod', [status(thm)], ['4', '7', '8', '9'])).
% 2.72/2.98  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('12', plain,
% 2.72/2.98      ((((k2_relat_1 @ sk_D) != (sk_A))
% 2.72/2.98        | ~ (v2_funct_1 @ sk_D)
% 2.72/2.98        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 2.72/2.98      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 2.72/2.98  thf('13', plain,
% 2.72/2.98      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.72/2.98        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.72/2.98        (k6_partfun1 @ sk_A))),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('14', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 2.72/2.98      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.72/2.98  thf('15', plain,
% 2.72/2.98      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.72/2.98        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.72/2.98        (k6_relat_1 @ sk_A))),
% 2.72/2.98      inference('demod', [status(thm)], ['13', '14'])).
% 2.72/2.98  thf('16', plain,
% 2.72/2.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('17', plain,
% 2.72/2.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf(dt_k1_partfun1, axiom,
% 2.72/2.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.72/2.98     ( ( ( v1_funct_1 @ E ) & 
% 2.72/2.98         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.72/2.98         ( v1_funct_1 @ F ) & 
% 2.72/2.98         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.72/2.98       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.72/2.98         ( m1_subset_1 @
% 2.72/2.98           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.72/2.98           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.72/2.98  thf('18', plain,
% 2.72/2.98      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 2.72/2.98         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 2.72/2.98          | ~ (v1_funct_1 @ X26)
% 2.72/2.98          | ~ (v1_funct_1 @ X29)
% 2.72/2.98          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 2.72/2.98          | (m1_subset_1 @ (k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29) @ 
% 2.72/2.98             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X31))))),
% 2.72/2.98      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.72/2.98  thf('19', plain,
% 2.72/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.98         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.72/2.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.72/2.98          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.72/2.98          | ~ (v1_funct_1 @ X1)
% 2.72/2.98          | ~ (v1_funct_1 @ sk_C))),
% 2.72/2.98      inference('sup-', [status(thm)], ['17', '18'])).
% 2.72/2.98  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('21', plain,
% 2.72/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.98         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.72/2.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.72/2.98          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.72/2.98          | ~ (v1_funct_1 @ X1))),
% 2.72/2.98      inference('demod', [status(thm)], ['19', '20'])).
% 2.72/2.98  thf('22', plain,
% 2.72/2.98      ((~ (v1_funct_1 @ sk_D)
% 2.72/2.98        | (m1_subset_1 @ 
% 2.72/2.98           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.72/2.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.72/2.98      inference('sup-', [status(thm)], ['16', '21'])).
% 2.72/2.98  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('24', plain,
% 2.72/2.98      ((m1_subset_1 @ 
% 2.72/2.98        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.72/2.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.72/2.98      inference('demod', [status(thm)], ['22', '23'])).
% 2.72/2.98  thf(redefinition_r2_relset_1, axiom,
% 2.72/2.98    (![A:$i,B:$i,C:$i,D:$i]:
% 2.72/2.98     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.72/2.98         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.72/2.98       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.72/2.98  thf('25', plain,
% 2.72/2.98      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 2.72/2.98         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 2.72/2.98          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 2.72/2.98          | ((X22) = (X25))
% 2.72/2.98          | ~ (r2_relset_1 @ X23 @ X24 @ X22 @ X25))),
% 2.72/2.98      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.72/2.98  thf('26', plain,
% 2.72/2.98      (![X0 : $i]:
% 2.72/2.98         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.72/2.98             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 2.72/2.98          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 2.72/2.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.72/2.98      inference('sup-', [status(thm)], ['24', '25'])).
% 2.72/2.98  thf('27', plain,
% 2.72/2.98      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 2.72/2.98           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.72/2.98        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.72/2.98            = (k6_relat_1 @ sk_A)))),
% 2.72/2.98      inference('sup-', [status(thm)], ['15', '26'])).
% 2.72/2.98  thf(dt_k6_partfun1, axiom,
% 2.72/2.98    (![A:$i]:
% 2.72/2.98     ( ( m1_subset_1 @
% 2.72/2.98         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 2.72/2.98       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 2.72/2.98  thf('28', plain,
% 2.72/2.98      (![X33 : $i]:
% 2.72/2.98         (m1_subset_1 @ (k6_partfun1 @ X33) @ 
% 2.72/2.98          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 2.72/2.98      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 2.72/2.98  thf('29', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 2.72/2.98      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.72/2.98  thf('30', plain,
% 2.72/2.98      (![X33 : $i]:
% 2.72/2.98         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 2.72/2.98          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 2.72/2.98      inference('demod', [status(thm)], ['28', '29'])).
% 2.72/2.98  thf('31', plain,
% 2.72/2.98      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.72/2.98         = (k6_relat_1 @ sk_A))),
% 2.72/2.98      inference('demod', [status(thm)], ['27', '30'])).
% 2.72/2.98  thf('32', plain,
% 2.72/2.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf(t24_funct_2, axiom,
% 2.72/2.98    (![A:$i,B:$i,C:$i]:
% 2.72/2.98     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.72/2.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.72/2.98       ( ![D:$i]:
% 2.72/2.98         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.72/2.98             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.72/2.98           ( ( r2_relset_1 @
% 2.72/2.98               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.72/2.98               ( k6_partfun1 @ B ) ) =>
% 2.72/2.98             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.72/2.98  thf('33', plain,
% 2.72/2.98      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 2.72/2.98         (~ (v1_funct_1 @ X41)
% 2.72/2.98          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 2.72/2.98          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 2.72/2.98          | ~ (r2_relset_1 @ X42 @ X42 @ 
% 2.72/2.98               (k1_partfun1 @ X42 @ X43 @ X43 @ X42 @ X41 @ X44) @ 
% 2.72/2.98               (k6_partfun1 @ X42))
% 2.72/2.98          | ((k2_relset_1 @ X43 @ X42 @ X44) = (X42))
% 2.72/2.98          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 2.72/2.98          | ~ (v1_funct_2 @ X44 @ X43 @ X42)
% 2.72/2.98          | ~ (v1_funct_1 @ X44))),
% 2.72/2.98      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.72/2.98  thf('34', plain, (![X40 : $i]: ((k6_partfun1 @ X40) = (k6_relat_1 @ X40))),
% 2.72/2.98      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.72/2.98  thf('35', plain,
% 2.72/2.98      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 2.72/2.98         (~ (v1_funct_1 @ X41)
% 2.72/2.98          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 2.72/2.98          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 2.72/2.98          | ~ (r2_relset_1 @ X42 @ X42 @ 
% 2.72/2.98               (k1_partfun1 @ X42 @ X43 @ X43 @ X42 @ X41 @ X44) @ 
% 2.72/2.98               (k6_relat_1 @ X42))
% 2.72/2.98          | ((k2_relset_1 @ X43 @ X42 @ X44) = (X42))
% 2.72/2.98          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 2.72/2.98          | ~ (v1_funct_2 @ X44 @ X43 @ X42)
% 2.72/2.98          | ~ (v1_funct_1 @ X44))),
% 2.72/2.98      inference('demod', [status(thm)], ['33', '34'])).
% 2.72/2.98  thf('36', plain,
% 2.72/2.98      (![X0 : $i]:
% 2.72/2.98         (~ (v1_funct_1 @ X0)
% 2.72/2.98          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.72/2.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.72/2.98          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.72/2.98          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.72/2.98               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.72/2.98               (k6_relat_1 @ sk_A))
% 2.72/2.98          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.72/2.98          | ~ (v1_funct_1 @ sk_C))),
% 2.72/2.98      inference('sup-', [status(thm)], ['32', '35'])).
% 2.72/2.98  thf('37', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('39', plain,
% 2.72/2.98      (![X0 : $i]:
% 2.72/2.98         (~ (v1_funct_1 @ X0)
% 2.72/2.98          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.72/2.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.72/2.98          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.72/2.98          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.72/2.98               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.72/2.98               (k6_relat_1 @ sk_A)))),
% 2.72/2.98      inference('demod', [status(thm)], ['36', '37', '38'])).
% 2.72/2.98  thf('40', plain,
% 2.72/2.98      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 2.72/2.98           (k6_relat_1 @ sk_A))
% 2.72/2.98        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 2.72/2.98        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.72/2.98        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.72/2.98        | ~ (v1_funct_1 @ sk_D))),
% 2.72/2.98      inference('sup-', [status(thm)], ['31', '39'])).
% 2.72/2.98  thf('41', plain,
% 2.72/2.98      (![X33 : $i]:
% 2.72/2.98         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 2.72/2.98          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 2.72/2.98      inference('demod', [status(thm)], ['28', '29'])).
% 2.72/2.98  thf('42', plain,
% 2.72/2.98      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 2.72/2.98         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 2.72/2.98          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 2.72/2.98          | (r2_relset_1 @ X23 @ X24 @ X22 @ X25)
% 2.72/2.98          | ((X22) != (X25)))),
% 2.72/2.98      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.72/2.98  thf('43', plain,
% 2.72/2.98      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.72/2.98         ((r2_relset_1 @ X23 @ X24 @ X25 @ X25)
% 2.72/2.98          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 2.72/2.98      inference('simplify', [status(thm)], ['42'])).
% 2.72/2.98  thf('44', plain,
% 2.72/2.98      (![X0 : $i]:
% 2.72/2.98         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 2.72/2.98      inference('sup-', [status(thm)], ['41', '43'])).
% 2.72/2.98  thf('45', plain,
% 2.72/2.98      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.72/2.98      inference('sup-', [status(thm)], ['5', '6'])).
% 2.72/2.98  thf('46', plain,
% 2.72/2.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('47', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('48', plain, ((v1_funct_1 @ sk_D)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('49', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.72/2.98      inference('demod', [status(thm)], ['40', '44', '45', '46', '47', '48'])).
% 2.72/2.98  thf('50', plain,
% 2.72/2.98      ((((sk_A) != (sk_A))
% 2.72/2.98        | ~ (v2_funct_1 @ sk_D)
% 2.72/2.98        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B)))),
% 2.72/2.98      inference('demod', [status(thm)], ['12', '49'])).
% 2.72/2.98  thf('51', plain,
% 2.72/2.98      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 2.72/2.98        | ~ (v2_funct_1 @ sk_D))),
% 2.72/2.98      inference('simplify', [status(thm)], ['50'])).
% 2.72/2.98  thf('52', plain,
% 2.72/2.98      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.72/2.98         = (k6_relat_1 @ sk_A))),
% 2.72/2.98      inference('demod', [status(thm)], ['27', '30'])).
% 2.72/2.98  thf('53', plain,
% 2.72/2.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf(t30_funct_2, axiom,
% 2.72/2.98    (![A:$i,B:$i,C:$i,D:$i]:
% 2.72/2.98     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.72/2.98         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 2.72/2.98       ( ![E:$i]:
% 2.72/2.98         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 2.72/2.98             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 2.72/2.98           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 2.72/2.98               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 2.72/2.98             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 2.72/2.98               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 2.72/2.98  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 2.72/2.98  thf(zf_stmt_2, axiom,
% 2.72/2.98    (![C:$i,B:$i]:
% 2.72/2.98     ( ( zip_tseitin_1 @ C @ B ) =>
% 2.72/2.98       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 2.72/2.98  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 2.72/2.98  thf(zf_stmt_4, axiom,
% 2.72/2.98    (![E:$i,D:$i]:
% 2.72/2.98     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 2.72/2.98  thf(zf_stmt_5, axiom,
% 2.72/2.98    (![A:$i,B:$i,C:$i,D:$i]:
% 2.72/2.98     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.72/2.98         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.72/2.98       ( ![E:$i]:
% 2.72/2.98         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.72/2.98             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.72/2.98           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 2.72/2.98               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 2.72/2.98             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 2.72/2.98  thf('54', plain,
% 2.72/2.98      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 2.72/2.98         (~ (v1_funct_1 @ X49)
% 2.72/2.98          | ~ (v1_funct_2 @ X49 @ X50 @ X51)
% 2.72/2.98          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 2.72/2.98          | (zip_tseitin_0 @ X49 @ X52)
% 2.72/2.98          | ~ (v2_funct_1 @ (k1_partfun1 @ X53 @ X50 @ X50 @ X51 @ X52 @ X49))
% 2.72/2.98          | (zip_tseitin_1 @ X51 @ X50)
% 2.72/2.98          | ((k2_relset_1 @ X53 @ X50 @ X52) != (X50))
% 2.72/2.98          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X50)))
% 2.72/2.98          | ~ (v1_funct_2 @ X52 @ X53 @ X50)
% 2.72/2.98          | ~ (v1_funct_1 @ X52))),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.72/2.98  thf('55', plain,
% 2.72/2.98      (![X0 : $i, X1 : $i]:
% 2.72/2.98         (~ (v1_funct_1 @ X0)
% 2.72/2.98          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.72/2.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.72/2.98          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 2.72/2.98          | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.72/2.98          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.72/2.98          | (zip_tseitin_0 @ sk_D @ X0)
% 2.72/2.98          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.72/2.98          | ~ (v1_funct_1 @ sk_D))),
% 2.72/2.98      inference('sup-', [status(thm)], ['53', '54'])).
% 2.72/2.98  thf('56', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('57', plain, ((v1_funct_1 @ sk_D)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('58', plain,
% 2.72/2.98      (![X0 : $i, X1 : $i]:
% 2.72/2.98         (~ (v1_funct_1 @ X0)
% 2.72/2.98          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.72/2.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.72/2.98          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 2.72/2.98          | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.72/2.98          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.72/2.98          | (zip_tseitin_0 @ sk_D @ X0))),
% 2.72/2.98      inference('demod', [status(thm)], ['55', '56', '57'])).
% 2.72/2.98  thf('59', plain,
% 2.72/2.98      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 2.72/2.98        | (zip_tseitin_0 @ sk_D @ sk_C)
% 2.72/2.98        | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.72/2.98        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.72/2.98        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.72/2.98        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.72/2.98        | ~ (v1_funct_1 @ sk_C))),
% 2.72/2.98      inference('sup-', [status(thm)], ['52', '58'])).
% 2.72/2.98  thf(fc4_funct_1, axiom,
% 2.72/2.98    (![A:$i]:
% 2.72/2.98     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.72/2.98       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.72/2.98  thf('60', plain, (![X15 : $i]: (v2_funct_1 @ (k6_relat_1 @ X15))),
% 2.72/2.98      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.72/2.98  thf('61', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('62', plain,
% 2.72/2.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('63', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('65', plain,
% 2.72/2.98      (((zip_tseitin_0 @ sk_D @ sk_C)
% 2.72/2.98        | (zip_tseitin_1 @ sk_A @ sk_B)
% 2.72/2.98        | ((sk_B) != (sk_B)))),
% 2.72/2.98      inference('demod', [status(thm)], ['59', '60', '61', '62', '63', '64'])).
% 2.72/2.98  thf('66', plain,
% 2.72/2.98      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 2.72/2.98      inference('simplify', [status(thm)], ['65'])).
% 2.72/2.98  thf('67', plain,
% 2.72/2.98      (![X47 : $i, X48 : $i]:
% 2.72/2.98         (((X47) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X47 @ X48))),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.72/2.98  thf('68', plain,
% 2.72/2.98      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.72/2.98      inference('sup-', [status(thm)], ['66', '67'])).
% 2.72/2.98  thf('69', plain, (((sk_A) != (k1_xboole_0))),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('70', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 2.72/2.98      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 2.72/2.98  thf('71', plain,
% 2.72/2.98      (![X45 : $i, X46 : $i]:
% 2.72/2.98         ((v2_funct_1 @ X46) | ~ (zip_tseitin_0 @ X46 @ X45))),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_4])).
% 2.72/2.98  thf('72', plain, ((v2_funct_1 @ sk_D)),
% 2.72/2.98      inference('sup-', [status(thm)], ['70', '71'])).
% 2.72/2.98  thf('73', plain,
% 2.72/2.98      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 2.72/2.98      inference('demod', [status(thm)], ['51', '72'])).
% 2.72/2.98  thf('74', plain,
% 2.72/2.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('75', plain,
% 2.72/2.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf(redefinition_k1_partfun1, axiom,
% 2.72/2.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.72/2.98     ( ( ( v1_funct_1 @ E ) & 
% 2.72/2.98         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.72/2.98         ( v1_funct_1 @ F ) & 
% 2.72/2.98         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.72/2.98       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.72/2.98  thf('76', plain,
% 2.72/2.98      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 2.72/2.98         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 2.72/2.98          | ~ (v1_funct_1 @ X34)
% 2.72/2.98          | ~ (v1_funct_1 @ X37)
% 2.72/2.98          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 2.72/2.98          | ((k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37)
% 2.72/2.98              = (k5_relat_1 @ X34 @ X37)))),
% 2.72/2.98      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.72/2.98  thf('77', plain,
% 2.72/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.98         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.72/2.98            = (k5_relat_1 @ sk_C @ X0))
% 2.72/2.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.72/2.98          | ~ (v1_funct_1 @ X0)
% 2.72/2.98          | ~ (v1_funct_1 @ sk_C))),
% 2.72/2.98      inference('sup-', [status(thm)], ['75', '76'])).
% 2.72/2.98  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('79', plain,
% 2.72/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.98         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 2.72/2.98            = (k5_relat_1 @ sk_C @ X0))
% 2.72/2.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.72/2.98          | ~ (v1_funct_1 @ X0))),
% 2.72/2.98      inference('demod', [status(thm)], ['77', '78'])).
% 2.72/2.98  thf('80', plain,
% 2.72/2.98      ((~ (v1_funct_1 @ sk_D)
% 2.72/2.98        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.72/2.98            = (k5_relat_1 @ sk_C @ sk_D)))),
% 2.72/2.98      inference('sup-', [status(thm)], ['74', '79'])).
% 2.72/2.98  thf('81', plain, ((v1_funct_1 @ sk_D)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('82', plain,
% 2.72/2.98      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.72/2.98         = (k6_relat_1 @ sk_A))),
% 2.72/2.98      inference('demod', [status(thm)], ['27', '30'])).
% 2.72/2.98  thf('83', plain, (((k6_relat_1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 2.72/2.98      inference('demod', [status(thm)], ['80', '81', '82'])).
% 2.72/2.98  thf(t64_funct_1, axiom,
% 2.72/2.98    (![A:$i]:
% 2.72/2.98     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.72/2.98       ( ![B:$i]:
% 2.72/2.98         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 2.72/2.98           ( ( ( v2_funct_1 @ A ) & 
% 2.72/2.98               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 2.72/2.98               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 2.72/2.98             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.72/2.98  thf('84', plain,
% 2.72/2.98      (![X17 : $i, X18 : $i]:
% 2.72/2.98         (~ (v1_relat_1 @ X17)
% 2.72/2.98          | ~ (v1_funct_1 @ X17)
% 2.72/2.98          | ((X17) = (k2_funct_1 @ X18))
% 2.72/2.98          | ((k5_relat_1 @ X17 @ X18) != (k6_relat_1 @ (k2_relat_1 @ X18)))
% 2.72/2.98          | ((k2_relat_1 @ X17) != (k1_relat_1 @ X18))
% 2.72/2.98          | ~ (v2_funct_1 @ X18)
% 2.72/2.98          | ~ (v1_funct_1 @ X18)
% 2.72/2.98          | ~ (v1_relat_1 @ X18))),
% 2.72/2.98      inference('cnf', [status(esa)], [t64_funct_1])).
% 2.72/2.98  thf('85', plain,
% 2.72/2.98      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k2_relat_1 @ sk_D)))
% 2.72/2.98        | ~ (v1_relat_1 @ sk_D)
% 2.72/2.98        | ~ (v1_funct_1 @ sk_D)
% 2.72/2.98        | ~ (v2_funct_1 @ sk_D)
% 2.72/2.98        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 2.72/2.98        | ((sk_C) = (k2_funct_1 @ sk_D))
% 2.72/2.98        | ~ (v1_funct_1 @ sk_C)
% 2.72/2.98        | ~ (v1_relat_1 @ sk_C))),
% 2.72/2.98      inference('sup-', [status(thm)], ['83', '84'])).
% 2.72/2.98  thf('86', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.72/2.98      inference('demod', [status(thm)], ['40', '44', '45', '46', '47', '48'])).
% 2.72/2.98  thf('87', plain,
% 2.72/2.98      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf(cc2_relat_1, axiom,
% 2.72/2.98    (![A:$i]:
% 2.72/2.98     ( ( v1_relat_1 @ A ) =>
% 2.72/2.98       ( ![B:$i]:
% 2.72/2.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.72/2.98  thf('88', plain,
% 2.72/2.98      (![X5 : $i, X6 : $i]:
% 2.72/2.98         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 2.72/2.98          | (v1_relat_1 @ X5)
% 2.72/2.98          | ~ (v1_relat_1 @ X6))),
% 2.72/2.98      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.72/2.98  thf('89', plain,
% 2.72/2.98      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 2.72/2.98      inference('sup-', [status(thm)], ['87', '88'])).
% 2.72/2.98  thf(fc6_relat_1, axiom,
% 2.72/2.98    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.72/2.98  thf('90', plain,
% 2.72/2.98      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 2.72/2.98      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.72/2.98  thf('91', plain, ((v1_relat_1 @ sk_D)),
% 2.72/2.98      inference('demod', [status(thm)], ['89', '90'])).
% 2.72/2.98  thf('92', plain, ((v1_funct_1 @ sk_D)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('93', plain,
% 2.72/2.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('94', plain,
% 2.72/2.98      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.72/2.98         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 2.72/2.98          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 2.72/2.98      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.72/2.98  thf('95', plain,
% 2.72/2.98      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 2.72/2.98      inference('sup-', [status(thm)], ['93', '94'])).
% 2.72/2.98  thf('96', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('97', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.72/2.98      inference('sup+', [status(thm)], ['95', '96'])).
% 2.72/2.98  thf('98', plain, ((v1_funct_1 @ sk_C)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('99', plain,
% 2.72/2.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('100', plain,
% 2.72/2.98      (![X5 : $i, X6 : $i]:
% 2.72/2.98         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 2.72/2.98          | (v1_relat_1 @ X5)
% 2.72/2.98          | ~ (v1_relat_1 @ X6))),
% 2.72/2.98      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.72/2.98  thf('101', plain,
% 2.72/2.98      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 2.72/2.98      inference('sup-', [status(thm)], ['99', '100'])).
% 2.72/2.98  thf('102', plain,
% 2.72/2.98      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 2.72/2.98      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.72/2.98  thf('103', plain, ((v1_relat_1 @ sk_C)),
% 2.72/2.98      inference('demod', [status(thm)], ['101', '102'])).
% 2.72/2.98  thf('104', plain,
% 2.72/2.98      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 2.72/2.98        | ~ (v2_funct_1 @ sk_D)
% 2.72/2.98        | ((sk_B) != (k1_relat_1 @ sk_D))
% 2.72/2.98        | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 2.72/2.98      inference('demod', [status(thm)],
% 2.72/2.98                ['85', '86', '91', '92', '97', '98', '103'])).
% 2.72/2.98  thf('105', plain,
% 2.72/2.98      ((((sk_C) = (k2_funct_1 @ sk_D))
% 2.72/2.98        | ((sk_B) != (k1_relat_1 @ sk_D))
% 2.72/2.98        | ~ (v2_funct_1 @ sk_D))),
% 2.72/2.98      inference('simplify', [status(thm)], ['104'])).
% 2.72/2.98  thf('106', plain, ((v2_funct_1 @ sk_D)),
% 2.72/2.98      inference('sup-', [status(thm)], ['70', '71'])).
% 2.72/2.98  thf('107', plain,
% 2.72/2.98      ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (k1_relat_1 @ sk_D)))),
% 2.72/2.98      inference('demod', [status(thm)], ['105', '106'])).
% 2.72/2.98  thf(t55_funct_1, axiom,
% 2.72/2.98    (![A:$i]:
% 2.72/2.98     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.72/2.98       ( ( v2_funct_1 @ A ) =>
% 2.72/2.98         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.72/2.98           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.72/2.98  thf('108', plain,
% 2.72/2.98      (![X16 : $i]:
% 2.72/2.98         (~ (v2_funct_1 @ X16)
% 2.72/2.98          | ((k1_relat_1 @ X16) = (k2_relat_1 @ (k2_funct_1 @ X16)))
% 2.72/2.98          | ~ (v1_funct_1 @ X16)
% 2.72/2.98          | ~ (v1_relat_1 @ X16))),
% 2.72/2.98      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.72/2.98  thf('109', plain,
% 2.72/2.98      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 2.72/2.98      inference('demod', [status(thm)], ['51', '72'])).
% 2.72/2.98  thf(dt_k2_funct_1, axiom,
% 2.72/2.98    (![A:$i]:
% 2.72/2.98     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.72/2.98       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.72/2.98         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.72/2.98  thf('110', plain,
% 2.72/2.98      (![X13 : $i]:
% 2.72/2.98         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 2.72/2.98          | ~ (v1_funct_1 @ X13)
% 2.72/2.98          | ~ (v1_relat_1 @ X13))),
% 2.72/2.98      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.72/2.98  thf(dt_k2_subset_1, axiom,
% 2.72/2.98    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 2.72/2.98  thf('111', plain,
% 2.72/2.98      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 2.72/2.98      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 2.72/2.98  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 2.72/2.98  thf('112', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 2.72/2.98      inference('cnf', [status(esa)], [d4_subset_1])).
% 2.72/2.98  thf('113', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 2.72/2.98      inference('demod', [status(thm)], ['111', '112'])).
% 2.72/2.98  thf(t3_subset, axiom,
% 2.72/2.98    (![A:$i,B:$i]:
% 2.72/2.98     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.72/2.98  thf('114', plain,
% 2.72/2.98      (![X2 : $i, X3 : $i]:
% 2.72/2.98         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 2.72/2.98      inference('cnf', [status(esa)], [t3_subset])).
% 2.72/2.98  thf('115', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 2.72/2.98      inference('sup-', [status(thm)], ['113', '114'])).
% 2.72/2.98  thf('116', plain,
% 2.72/2.98      (![X16 : $i]:
% 2.72/2.98         (~ (v2_funct_1 @ X16)
% 2.72/2.98          | ((k2_relat_1 @ X16) = (k1_relat_1 @ (k2_funct_1 @ X16)))
% 2.72/2.98          | ~ (v1_funct_1 @ X16)
% 2.72/2.98          | ~ (v1_relat_1 @ X16))),
% 2.72/2.98      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.72/2.98  thf(t47_relat_1, axiom,
% 2.72/2.98    (![A:$i]:
% 2.72/2.98     ( ( v1_relat_1 @ A ) =>
% 2.72/2.98       ( ![B:$i]:
% 2.72/2.98         ( ( v1_relat_1 @ B ) =>
% 2.72/2.98           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 2.72/2.98             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.72/2.98  thf('117', plain,
% 2.72/2.98      (![X9 : $i, X10 : $i]:
% 2.72/2.98         (~ (v1_relat_1 @ X9)
% 2.72/2.98          | ((k2_relat_1 @ (k5_relat_1 @ X9 @ X10)) = (k2_relat_1 @ X10))
% 2.72/2.98          | ~ (r1_tarski @ (k1_relat_1 @ X10) @ (k2_relat_1 @ X9))
% 2.72/2.98          | ~ (v1_relat_1 @ X10))),
% 2.72/2.98      inference('cnf', [status(esa)], [t47_relat_1])).
% 2.72/2.98  thf('118', plain,
% 2.72/2.98      (![X0 : $i, X1 : $i]:
% 2.72/2.98         (~ (r1_tarski @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X1))
% 2.72/2.98          | ~ (v1_relat_1 @ X0)
% 2.72/2.98          | ~ (v1_funct_1 @ X0)
% 2.72/2.98          | ~ (v2_funct_1 @ X0)
% 2.72/2.98          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.72/2.98          | ((k2_relat_1 @ (k5_relat_1 @ X1 @ (k2_funct_1 @ X0)))
% 2.72/2.98              = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.72/2.98          | ~ (v1_relat_1 @ X1))),
% 2.72/2.98      inference('sup-', [status(thm)], ['116', '117'])).
% 2.72/2.98  thf('119', plain,
% 2.72/2.98      (![X0 : $i]:
% 2.72/2.98         (~ (v1_relat_1 @ X0)
% 2.72/2.98          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 2.72/2.98              = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.72/2.98          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.72/2.98          | ~ (v2_funct_1 @ X0)
% 2.72/2.98          | ~ (v1_funct_1 @ X0)
% 2.72/2.98          | ~ (v1_relat_1 @ X0))),
% 2.72/2.98      inference('sup-', [status(thm)], ['115', '118'])).
% 2.72/2.98  thf('120', plain,
% 2.72/2.98      (![X0 : $i]:
% 2.72/2.98         (~ (v1_funct_1 @ X0)
% 2.72/2.98          | ~ (v2_funct_1 @ X0)
% 2.72/2.98          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.72/2.98          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 2.72/2.98              = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.72/2.98          | ~ (v1_relat_1 @ X0))),
% 2.72/2.98      inference('simplify', [status(thm)], ['119'])).
% 2.72/2.98  thf('121', plain,
% 2.72/2.98      (![X0 : $i]:
% 2.72/2.98         (~ (v1_relat_1 @ X0)
% 2.72/2.98          | ~ (v1_funct_1 @ X0)
% 2.72/2.98          | ~ (v1_relat_1 @ X0)
% 2.72/2.98          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 2.72/2.98              = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.72/2.98          | ~ (v2_funct_1 @ X0)
% 2.72/2.98          | ~ (v1_funct_1 @ X0))),
% 2.72/2.98      inference('sup-', [status(thm)], ['110', '120'])).
% 2.72/2.98  thf('122', plain,
% 2.72/2.98      (![X0 : $i]:
% 2.72/2.98         (~ (v2_funct_1 @ X0)
% 2.72/2.98          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 2.72/2.98              = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.72/2.98          | ~ (v1_funct_1 @ X0)
% 2.72/2.98          | ~ (v1_relat_1 @ X0))),
% 2.72/2.98      inference('simplify', [status(thm)], ['121'])).
% 2.72/2.98  thf('123', plain,
% 2.72/2.98      ((((k2_relat_1 @ (k6_relat_1 @ sk_B))
% 2.72/2.98          = (k2_relat_1 @ (k2_funct_1 @ sk_D)))
% 2.72/2.98        | ~ (v1_relat_1 @ sk_D)
% 2.72/2.98        | ~ (v1_funct_1 @ sk_D)
% 2.72/2.98        | ~ (v2_funct_1 @ sk_D))),
% 2.72/2.98      inference('sup+', [status(thm)], ['109', '122'])).
% 2.72/2.98  thf(t71_relat_1, axiom,
% 2.72/2.98    (![A:$i]:
% 2.72/2.98     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.72/2.98       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.72/2.98  thf('124', plain, (![X12 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 2.72/2.98      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.72/2.98  thf('125', plain, ((v1_relat_1 @ sk_D)),
% 2.72/2.98      inference('demod', [status(thm)], ['89', '90'])).
% 2.72/2.98  thf('126', plain, ((v1_funct_1 @ sk_D)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('127', plain, ((v2_funct_1 @ sk_D)),
% 2.72/2.98      inference('sup-', [status(thm)], ['70', '71'])).
% 2.72/2.98  thf('128', plain, (((sk_B) = (k2_relat_1 @ (k2_funct_1 @ sk_D)))),
% 2.72/2.98      inference('demod', [status(thm)], ['123', '124', '125', '126', '127'])).
% 2.72/2.98  thf('129', plain,
% 2.72/2.98      ((((sk_B) = (k1_relat_1 @ sk_D))
% 2.72/2.98        | ~ (v1_relat_1 @ sk_D)
% 2.72/2.98        | ~ (v1_funct_1 @ sk_D)
% 2.72/2.98        | ~ (v2_funct_1 @ sk_D))),
% 2.72/2.98      inference('sup+', [status(thm)], ['108', '128'])).
% 2.72/2.98  thf('130', plain, ((v1_relat_1 @ sk_D)),
% 2.72/2.98      inference('demod', [status(thm)], ['89', '90'])).
% 2.72/2.98  thf('131', plain, ((v1_funct_1 @ sk_D)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('132', plain, ((v2_funct_1 @ sk_D)),
% 2.72/2.98      inference('sup-', [status(thm)], ['70', '71'])).
% 2.72/2.98  thf('133', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 2.72/2.98      inference('demod', [status(thm)], ['129', '130', '131', '132'])).
% 2.72/2.98  thf('134', plain, ((((sk_C) = (k2_funct_1 @ sk_D)) | ((sk_B) != (sk_B)))),
% 2.72/2.98      inference('demod', [status(thm)], ['107', '133'])).
% 2.72/2.98  thf('135', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 2.72/2.98      inference('simplify', [status(thm)], ['134'])).
% 2.72/2.98  thf('136', plain, (((k5_relat_1 @ sk_D @ sk_C) = (k6_relat_1 @ sk_B))),
% 2.72/2.98      inference('demod', [status(thm)], ['73', '135'])).
% 2.72/2.98  thf('137', plain,
% 2.72/2.98      (![X17 : $i, X18 : $i]:
% 2.72/2.98         (~ (v1_relat_1 @ X17)
% 2.72/2.98          | ~ (v1_funct_1 @ X17)
% 2.72/2.98          | ((X17) = (k2_funct_1 @ X18))
% 2.72/2.98          | ((k5_relat_1 @ X17 @ X18) != (k6_relat_1 @ (k2_relat_1 @ X18)))
% 2.72/2.98          | ((k2_relat_1 @ X17) != (k1_relat_1 @ X18))
% 2.72/2.98          | ~ (v2_funct_1 @ X18)
% 2.72/2.98          | ~ (v1_funct_1 @ X18)
% 2.72/2.98          | ~ (v1_relat_1 @ X18))),
% 2.72/2.98      inference('cnf', [status(esa)], [t64_funct_1])).
% 2.72/2.98  thf('138', plain,
% 2.72/2.98      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ (k2_relat_1 @ sk_C)))
% 2.72/2.98        | ~ (v1_relat_1 @ sk_C)
% 2.72/2.98        | ~ (v1_funct_1 @ sk_C)
% 2.72/2.98        | ~ (v2_funct_1 @ sk_C)
% 2.72/2.98        | ((k2_relat_1 @ sk_D) != (k1_relat_1 @ sk_C))
% 2.72/2.98        | ((sk_D) = (k2_funct_1 @ sk_C))
% 2.72/2.98        | ~ (v1_funct_1 @ sk_D)
% 2.72/2.98        | ~ (v1_relat_1 @ sk_D))),
% 2.72/2.98      inference('sup-', [status(thm)], ['136', '137'])).
% 2.72/2.98  thf('139', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.72/2.98      inference('sup+', [status(thm)], ['95', '96'])).
% 2.72/2.98  thf('140', plain, ((v1_relat_1 @ sk_C)),
% 2.72/2.98      inference('demod', [status(thm)], ['101', '102'])).
% 2.72/2.98  thf('141', plain, ((v1_funct_1 @ sk_C)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('142', plain, ((v2_funct_1 @ sk_C)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('143', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.72/2.98      inference('demod', [status(thm)], ['40', '44', '45', '46', '47', '48'])).
% 2.72/2.98  thf('144', plain,
% 2.72/2.98      (![X16 : $i]:
% 2.72/2.98         (~ (v2_funct_1 @ X16)
% 2.72/2.98          | ((k1_relat_1 @ X16) = (k2_relat_1 @ (k2_funct_1 @ X16)))
% 2.72/2.98          | ~ (v1_funct_1 @ X16)
% 2.72/2.98          | ~ (v1_relat_1 @ X16))),
% 2.72/2.98      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.72/2.98  thf('145', plain,
% 2.72/2.98      (![X13 : $i]:
% 2.72/2.98         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 2.72/2.98          | ~ (v1_funct_1 @ X13)
% 2.72/2.98          | ~ (v1_relat_1 @ X13))),
% 2.72/2.98      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.72/2.98  thf('146', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.72/2.98      inference('sup+', [status(thm)], ['95', '96'])).
% 2.72/2.98  thf('147', plain,
% 2.72/2.98      (![X16 : $i]:
% 2.72/2.98         (~ (v2_funct_1 @ X16)
% 2.72/2.98          | ((k2_relat_1 @ X16) = (k1_relat_1 @ (k2_funct_1 @ X16)))
% 2.72/2.98          | ~ (v1_funct_1 @ X16)
% 2.72/2.98          | ~ (v1_relat_1 @ X16))),
% 2.72/2.98      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.72/2.98  thf('148', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.72/2.98      inference('sup+', [status(thm)], ['95', '96'])).
% 2.72/2.98  thf('149', plain,
% 2.72/2.98      (![X9 : $i, X10 : $i]:
% 2.72/2.98         (~ (v1_relat_1 @ X9)
% 2.72/2.98          | ((k2_relat_1 @ (k5_relat_1 @ X9 @ X10)) = (k2_relat_1 @ X10))
% 2.72/2.98          | ~ (r1_tarski @ (k1_relat_1 @ X10) @ (k2_relat_1 @ X9))
% 2.72/2.98          | ~ (v1_relat_1 @ X10))),
% 2.72/2.98      inference('cnf', [status(esa)], [t47_relat_1])).
% 2.72/2.98  thf('150', plain,
% 2.72/2.98      (![X0 : $i]:
% 2.72/2.98         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_B)
% 2.72/2.98          | ~ (v1_relat_1 @ X0)
% 2.72/2.98          | ((k2_relat_1 @ (k5_relat_1 @ sk_C @ X0)) = (k2_relat_1 @ X0))
% 2.72/2.98          | ~ (v1_relat_1 @ sk_C))),
% 2.72/2.98      inference('sup-', [status(thm)], ['148', '149'])).
% 2.72/2.98  thf('151', plain, ((v1_relat_1 @ sk_C)),
% 2.72/2.98      inference('demod', [status(thm)], ['101', '102'])).
% 2.72/2.98  thf('152', plain,
% 2.72/2.98      (![X0 : $i]:
% 2.72/2.98         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_B)
% 2.72/2.98          | ~ (v1_relat_1 @ X0)
% 2.72/2.98          | ((k2_relat_1 @ (k5_relat_1 @ sk_C @ X0)) = (k2_relat_1 @ X0)))),
% 2.72/2.98      inference('demod', [status(thm)], ['150', '151'])).
% 2.72/2.98  thf('153', plain,
% 2.72/2.98      (![X0 : $i]:
% 2.72/2.98         (~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_B)
% 2.72/2.98          | ~ (v1_relat_1 @ X0)
% 2.72/2.98          | ~ (v1_funct_1 @ X0)
% 2.72/2.98          | ~ (v2_funct_1 @ X0)
% 2.72/2.98          | ((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ X0)))
% 2.72/2.98              = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.72/2.98          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.72/2.98      inference('sup-', [status(thm)], ['147', '152'])).
% 2.72/2.98  thf('154', plain,
% 2.72/2.98      ((~ (r1_tarski @ sk_B @ sk_B)
% 2.72/2.98        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.72/2.98        | ((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 2.72/2.98            = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.72/2.98        | ~ (v2_funct_1 @ sk_C)
% 2.72/2.98        | ~ (v1_funct_1 @ sk_C)
% 2.72/2.98        | ~ (v1_relat_1 @ sk_C))),
% 2.72/2.98      inference('sup-', [status(thm)], ['146', '153'])).
% 2.72/2.98  thf('155', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 2.72/2.98      inference('sup-', [status(thm)], ['113', '114'])).
% 2.72/2.98  thf('156', plain, ((v2_funct_1 @ sk_C)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('157', plain, ((v1_funct_1 @ sk_C)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('158', plain, ((v1_relat_1 @ sk_C)),
% 2.72/2.98      inference('demod', [status(thm)], ['101', '102'])).
% 2.72/2.98  thf('159', plain,
% 2.72/2.98      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.72/2.98        | ((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 2.72/2.98            = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 2.72/2.98      inference('demod', [status(thm)], ['154', '155', '156', '157', '158'])).
% 2.72/2.98  thf('160', plain,
% 2.72/2.98      ((~ (v1_relat_1 @ sk_C)
% 2.72/2.98        | ~ (v1_funct_1 @ sk_C)
% 2.72/2.98        | ((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 2.72/2.98            = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 2.72/2.98      inference('sup-', [status(thm)], ['145', '159'])).
% 2.72/2.98  thf('161', plain, ((v1_relat_1 @ sk_C)),
% 2.72/2.98      inference('demod', [status(thm)], ['101', '102'])).
% 2.72/2.98  thf('162', plain, ((v1_funct_1 @ sk_C)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('163', plain,
% 2.72/2.98      (((k2_relat_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 2.72/2.98         = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.72/2.98      inference('demod', [status(thm)], ['160', '161', '162'])).
% 2.72/2.98  thf('164', plain,
% 2.72/2.98      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('165', plain,
% 2.72/2.98      (![X54 : $i, X55 : $i, X56 : $i]:
% 2.72/2.98         (((X54) = (k1_xboole_0))
% 2.72/2.98          | ~ (v1_funct_1 @ X55)
% 2.72/2.98          | ~ (v1_funct_2 @ X55 @ X56 @ X54)
% 2.72/2.98          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X54)))
% 2.72/2.98          | ((k5_relat_1 @ X55 @ (k2_funct_1 @ X55)) = (k6_relat_1 @ X56))
% 2.72/2.98          | ~ (v2_funct_1 @ X55)
% 2.72/2.98          | ((k2_relset_1 @ X56 @ X54 @ X55) != (X54)))),
% 2.72/2.98      inference('demod', [status(thm)], ['1', '2'])).
% 2.72/2.98  thf('166', plain,
% 2.72/2.98      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 2.72/2.98        | ~ (v2_funct_1 @ sk_C)
% 2.72/2.98        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 2.72/2.98        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.72/2.98        | ~ (v1_funct_1 @ sk_C)
% 2.72/2.98        | ((sk_B) = (k1_xboole_0)))),
% 2.72/2.98      inference('sup-', [status(thm)], ['164', '165'])).
% 2.72/2.98  thf('167', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('168', plain, ((v2_funct_1 @ sk_C)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('169', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('170', plain, ((v1_funct_1 @ sk_C)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('171', plain,
% 2.72/2.98      ((((sk_B) != (sk_B))
% 2.72/2.98        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 2.72/2.98        | ((sk_B) = (k1_xboole_0)))),
% 2.72/2.98      inference('demod', [status(thm)], ['166', '167', '168', '169', '170'])).
% 2.72/2.98  thf('172', plain,
% 2.72/2.98      ((((sk_B) = (k1_xboole_0))
% 2.72/2.98        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A)))),
% 2.72/2.98      inference('simplify', [status(thm)], ['171'])).
% 2.72/2.98  thf('173', plain, (((sk_B) != (k1_xboole_0))),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('174', plain,
% 2.72/2.98      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 2.72/2.98      inference('simplify_reflect-', [status(thm)], ['172', '173'])).
% 2.72/2.98  thf('175', plain, (![X12 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 2.72/2.98      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.72/2.98  thf('176', plain, (((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 2.72/2.98      inference('demod', [status(thm)], ['163', '174', '175'])).
% 2.72/2.98  thf('177', plain,
% 2.72/2.98      ((((sk_A) = (k1_relat_1 @ sk_C))
% 2.72/2.98        | ~ (v1_relat_1 @ sk_C)
% 2.72/2.98        | ~ (v1_funct_1 @ sk_C)
% 2.72/2.98        | ~ (v2_funct_1 @ sk_C))),
% 2.72/2.98      inference('sup+', [status(thm)], ['144', '176'])).
% 2.72/2.98  thf('178', plain, ((v1_relat_1 @ sk_C)),
% 2.72/2.98      inference('demod', [status(thm)], ['101', '102'])).
% 2.72/2.98  thf('179', plain, ((v1_funct_1 @ sk_C)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('180', plain, ((v2_funct_1 @ sk_C)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('181', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 2.72/2.98      inference('demod', [status(thm)], ['177', '178', '179', '180'])).
% 2.72/2.98  thf('182', plain, ((v1_funct_1 @ sk_D)),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('183', plain, ((v1_relat_1 @ sk_D)),
% 2.72/2.98      inference('demod', [status(thm)], ['89', '90'])).
% 2.72/2.98  thf('184', plain,
% 2.72/2.98      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ sk_B))
% 2.72/2.98        | ((sk_A) != (sk_A))
% 2.72/2.98        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 2.72/2.98      inference('demod', [status(thm)],
% 2.72/2.98                ['138', '139', '140', '141', '142', '143', '181', '182', '183'])).
% 2.72/2.98  thf('185', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 2.72/2.98      inference('simplify', [status(thm)], ['184'])).
% 2.72/2.98  thf('186', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 2.72/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.98  thf('187', plain, ($false),
% 2.72/2.98      inference('simplify_reflect-', [status(thm)], ['185', '186'])).
% 2.72/2.98  
% 2.72/2.98  % SZS output end Refutation
% 2.72/2.98  
% 2.72/2.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
