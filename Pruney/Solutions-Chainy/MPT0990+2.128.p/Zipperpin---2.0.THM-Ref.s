%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cEd1D262p1

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:16 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 240 expanded)
%              Number of leaves         :   41 (  89 expanded)
%              Depth                    :   13
%              Number of atoms          : 1181 (4674 expanded)
%              Number of equality atoms :   59 ( 299 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 )
        = ( k5_relat_1 @ X37 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('20',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('21',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( X26 = X29 )
      | ~ ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','22'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('24',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('25',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('26',plain,(
    ! [X30: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('28',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
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

thf('29',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X19 ) @ X19 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('30',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('31',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X19 ) @ X19 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) @ X10 )
        = ( k5_relat_1 @ X9 @ ( k5_relat_1 @ X8 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['27','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
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
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('44',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('45',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['43','44'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('51',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('52',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['47','52'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('54',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X12 ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('55',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('56',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X11 ) @ X12 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X12 ) @ X11 )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['50','51'])).

thf('59',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('63',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['65','70'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('72',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k1_relat_1 @ X18 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('73',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ( ( k5_relat_1 @ X13 @ ( k6_relat_1 @ X14 ) )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('74',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('75',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ( ( k5_relat_1 @ X13 @ ( k6_partfun1 @ X14 ) )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ X1 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['68','69'])).

thf('81',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['68','69'])).

thf('84',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['68','69'])).

thf('87',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['50','51'])).

thf('90',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['37','42','59','85','86','87','88','89'])).

thf('91',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['90','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cEd1D262p1
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:05:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 337 iterations in 0.181s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.64  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.46/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.64  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.64  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.64  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.46/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.46/0.64  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.46/0.64  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.64  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.46/0.64  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.46/0.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.64  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.46/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.64  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.64  thf(t36_funct_2, conjecture,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.64       ( ![D:$i]:
% 0.46/0.64         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.46/0.64             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.46/0.64           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.46/0.64               ( r2_relset_1 @
% 0.46/0.64                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.46/0.64                 ( k6_partfun1 @ A ) ) & 
% 0.46/0.64               ( v2_funct_1 @ C ) ) =>
% 0.46/0.64             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.46/0.64               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.64        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.64            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.64          ( ![D:$i]:
% 0.46/0.64            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.46/0.64                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.46/0.64              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.46/0.64                  ( r2_relset_1 @
% 0.46/0.64                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.46/0.64                    ( k6_partfun1 @ A ) ) & 
% 0.46/0.64                  ( v2_funct_1 @ C ) ) =>
% 0.46/0.64                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.46/0.64                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.46/0.64  thf('0', plain,
% 0.46/0.64      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.46/0.64        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.46/0.64        (k6_partfun1 @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(redefinition_k1_partfun1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.46/0.64     ( ( ( v1_funct_1 @ E ) & 
% 0.46/0.64         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.64         ( v1_funct_1 @ F ) & 
% 0.46/0.64         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.46/0.64       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.46/0.64          | ~ (v1_funct_1 @ X37)
% 0.46/0.64          | ~ (v1_funct_1 @ X40)
% 0.46/0.64          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.46/0.64          | ((k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)
% 0.46/0.64              = (k5_relat_1 @ X37 @ X40)))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.46/0.64            = (k5_relat_1 @ sk_C @ X0))
% 0.46/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.64  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.46/0.64            = (k5_relat_1 @ sk_C @ X0))
% 0.46/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.46/0.64          | ~ (v1_funct_1 @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['4', '5'])).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      ((~ (v1_funct_1 @ sk_D)
% 0.46/0.64        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.46/0.64            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['1', '6'])).
% 0.46/0.64  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.46/0.64         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.46/0.64      inference('demod', [status(thm)], ['7', '8'])).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.46/0.64        (k6_partfun1 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['0', '9'])).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(dt_k1_partfun1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.46/0.64     ( ( ( v1_funct_1 @ E ) & 
% 0.46/0.64         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.64         ( v1_funct_1 @ F ) & 
% 0.46/0.64         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.46/0.64       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.46/0.64         ( m1_subset_1 @
% 0.46/0.64           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.46/0.64           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.46/0.64          | ~ (v1_funct_1 @ X31)
% 0.46/0.64          | ~ (v1_funct_1 @ X34)
% 0.46/0.64          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.46/0.64          | (m1_subset_1 @ (k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34) @ 
% 0.46/0.64             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X36))))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.46/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.46/0.64          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.46/0.64          | ~ (v1_funct_1 @ X1)
% 0.46/0.64          | ~ (v1_funct_1 @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['12', '13'])).
% 0.46/0.64  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('16', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.46/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.46/0.64          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.46/0.64          | ~ (v1_funct_1 @ X1))),
% 0.46/0.64      inference('demod', [status(thm)], ['14', '15'])).
% 0.46/0.64  thf('17', plain,
% 0.46/0.64      ((~ (v1_funct_1 @ sk_D)
% 0.46/0.64        | (m1_subset_1 @ 
% 0.46/0.64           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.46/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['11', '16'])).
% 0.46/0.64  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.46/0.64         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.46/0.64      inference('demod', [status(thm)], ['7', '8'])).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.46/0.64        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.46/0.64  thf(redefinition_r2_relset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.64     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.64       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.46/0.64          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.46/0.64          | ((X26) = (X29))
% 0.46/0.64          | ~ (r2_relset_1 @ X27 @ X28 @ X26 @ X29))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.46/0.64          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.46/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.64  thf('23', plain,
% 0.46/0.64      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.46/0.64           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.46/0.64        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['10', '22'])).
% 0.46/0.64  thf(t29_relset_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( m1_subset_1 @
% 0.46/0.64       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      (![X30 : $i]:
% 0.46/0.64         (m1_subset_1 @ (k6_relat_1 @ X30) @ 
% 0.46/0.64          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 0.46/0.64      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.46/0.64  thf(redefinition_k6_partfun1, axiom,
% 0.46/0.64    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.46/0.64  thf('25', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (![X30 : $i]:
% 0.46/0.64         (m1_subset_1 @ (k6_partfun1 @ X30) @ 
% 0.46/0.64          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))),
% 0.46/0.64      inference('demod', [status(thm)], ['24', '25'])).
% 0.46/0.64  thf('27', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['23', '26'])).
% 0.46/0.64  thf(dt_k2_funct_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.64       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.46/0.64         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      (![X15 : $i]:
% 0.46/0.64         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.46/0.64          | ~ (v1_funct_1 @ X15)
% 0.46/0.64          | ~ (v1_relat_1 @ X15))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.64  thf(t61_funct_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.64       ( ( v2_funct_1 @ A ) =>
% 0.46/0.64         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.46/0.64             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.46/0.64           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.46/0.64             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      (![X19 : $i]:
% 0.46/0.64         (~ (v2_funct_1 @ X19)
% 0.46/0.64          | ((k5_relat_1 @ (k2_funct_1 @ X19) @ X19)
% 0.46/0.64              = (k6_relat_1 @ (k2_relat_1 @ X19)))
% 0.46/0.64          | ~ (v1_funct_1 @ X19)
% 0.46/0.64          | ~ (v1_relat_1 @ X19))),
% 0.46/0.64      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.46/0.64  thf('30', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.46/0.64  thf('31', plain,
% 0.46/0.64      (![X19 : $i]:
% 0.46/0.64         (~ (v2_funct_1 @ X19)
% 0.46/0.64          | ((k5_relat_1 @ (k2_funct_1 @ X19) @ X19)
% 0.46/0.64              = (k6_partfun1 @ (k2_relat_1 @ X19)))
% 0.46/0.64          | ~ (v1_funct_1 @ X19)
% 0.46/0.64          | ~ (v1_relat_1 @ X19))),
% 0.46/0.64      inference('demod', [status(thm)], ['29', '30'])).
% 0.46/0.64  thf(t55_relat_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ A ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( v1_relat_1 @ B ) =>
% 0.46/0.64           ( ![C:$i]:
% 0.46/0.64             ( ( v1_relat_1 @ C ) =>
% 0.46/0.64               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.46/0.64                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X8)
% 0.46/0.64          | ((k5_relat_1 @ (k5_relat_1 @ X9 @ X8) @ X10)
% 0.46/0.64              = (k5_relat_1 @ X9 @ (k5_relat_1 @ X8 @ X10)))
% 0.46/0.64          | ~ (v1_relat_1 @ X10)
% 0.46/0.64          | ~ (v1_relat_1 @ X9))),
% 0.46/0.64      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 0.46/0.64            = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ X1)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('sup+', [status(thm)], ['31', '32'])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X1)
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 0.46/0.64              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1))))),
% 0.46/0.64      inference('simplify', [status(thm)], ['33'])).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 0.46/0.64              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['28', '34'])).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X1)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 0.46/0.64              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['35'])).
% 0.46/0.64  thf('37', plain,
% 0.46/0.64      ((((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ sk_D)
% 0.46/0.64          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 0.46/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v1_relat_1 @ sk_D))),
% 0.46/0.64      inference('sup+', [status(thm)], ['27', '36'])).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.46/0.64         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 0.46/0.64          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('41', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('42', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.46/0.64      inference('sup+', [status(thm)], ['40', '41'])).
% 0.46/0.64  thf('43', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(cc2_relset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.64         ((v4_relat_1 @ X20 @ X21)
% 0.46/0.64          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.64  thf('45', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 0.46/0.64      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.64  thf(d18_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ B ) =>
% 0.46/0.64       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.46/0.64  thf('46', plain,
% 0.46/0.64      (![X2 : $i, X3 : $i]:
% 0.46/0.64         (~ (v4_relat_1 @ X2 @ X3)
% 0.46/0.64          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 0.46/0.64          | ~ (v1_relat_1 @ X2))),
% 0.46/0.64      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.46/0.64  thf('47', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['45', '46'])).
% 0.46/0.64  thf('48', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(cc2_relat_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ A ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.46/0.64  thf('49', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.46/0.64          | (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.64  thf('50', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.46/0.64      inference('sup-', [status(thm)], ['48', '49'])).
% 0.46/0.64  thf(fc6_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.46/0.64  thf('51', plain,
% 0.46/0.64      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.64  thf('52', plain, ((v1_relat_1 @ sk_D)),
% 0.46/0.64      inference('demod', [status(thm)], ['50', '51'])).
% 0.46/0.64  thf('53', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 0.46/0.64      inference('demod', [status(thm)], ['47', '52'])).
% 0.46/0.64  thf(t77_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ B ) =>
% 0.46/0.64       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.46/0.64         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.46/0.64  thf('54', plain,
% 0.46/0.64      (![X11 : $i, X12 : $i]:
% 0.46/0.64         (~ (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 0.46/0.64          | ((k5_relat_1 @ (k6_relat_1 @ X12) @ X11) = (X11))
% 0.46/0.64          | ~ (v1_relat_1 @ X11))),
% 0.46/0.64      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.46/0.64  thf('55', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.46/0.64  thf('56', plain,
% 0.46/0.64      (![X11 : $i, X12 : $i]:
% 0.46/0.64         (~ (r1_tarski @ (k1_relat_1 @ X11) @ X12)
% 0.46/0.64          | ((k5_relat_1 @ (k6_partfun1 @ X12) @ X11) = (X11))
% 0.46/0.64          | ~ (v1_relat_1 @ X11))),
% 0.46/0.64      inference('demod', [status(thm)], ['54', '55'])).
% 0.46/0.64  thf('57', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ sk_D)
% 0.46/0.64        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['53', '56'])).
% 0.46/0.64  thf('58', plain, ((v1_relat_1 @ sk_D)),
% 0.46/0.64      inference('demod', [status(thm)], ['50', '51'])).
% 0.46/0.64  thf('59', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 0.46/0.64      inference('demod', [status(thm)], ['57', '58'])).
% 0.46/0.64  thf('60', plain,
% 0.46/0.64      (![X15 : $i]:
% 0.46/0.64         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 0.46/0.64          | ~ (v1_funct_1 @ X15)
% 0.46/0.64          | ~ (v1_relat_1 @ X15))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.64  thf('61', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('62', plain,
% 0.46/0.64      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.64         ((v4_relat_1 @ X20 @ X21)
% 0.46/0.64          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.64  thf('63', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.46/0.64      inference('sup-', [status(thm)], ['61', '62'])).
% 0.46/0.64  thf('64', plain,
% 0.46/0.64      (![X2 : $i, X3 : $i]:
% 0.46/0.64         (~ (v4_relat_1 @ X2 @ X3)
% 0.46/0.64          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 0.46/0.64          | ~ (v1_relat_1 @ X2))),
% 0.46/0.64      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.46/0.64  thf('65', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['63', '64'])).
% 0.46/0.64  thf('66', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('67', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.46/0.64          | (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.64  thf('68', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['66', '67'])).
% 0.46/0.64  thf('69', plain,
% 0.46/0.64      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.64  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['68', '69'])).
% 0.46/0.64  thf('71', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.46/0.64      inference('demod', [status(thm)], ['65', '70'])).
% 0.46/0.64  thf(t55_funct_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.64       ( ( v2_funct_1 @ A ) =>
% 0.46/0.64         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.46/0.64           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.46/0.64  thf('72', plain,
% 0.46/0.64      (![X18 : $i]:
% 0.46/0.64         (~ (v2_funct_1 @ X18)
% 0.46/0.64          | ((k1_relat_1 @ X18) = (k2_relat_1 @ (k2_funct_1 @ X18)))
% 0.46/0.64          | ~ (v1_funct_1 @ X18)
% 0.46/0.64          | ~ (v1_relat_1 @ X18))),
% 0.46/0.64      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.64  thf(t79_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ B ) =>
% 0.46/0.64       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.46/0.64         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.46/0.64  thf('73', plain,
% 0.46/0.64      (![X13 : $i, X14 : $i]:
% 0.46/0.64         (~ (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 0.46/0.64          | ((k5_relat_1 @ X13 @ (k6_relat_1 @ X14)) = (X13))
% 0.46/0.64          | ~ (v1_relat_1 @ X13))),
% 0.46/0.64      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.46/0.64  thf('74', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.46/0.64  thf('75', plain,
% 0.46/0.64      (![X13 : $i, X14 : $i]:
% 0.46/0.64         (~ (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 0.46/0.64          | ((k5_relat_1 @ X13 @ (k6_partfun1 @ X14)) = (X13))
% 0.46/0.64          | ~ (v1_relat_1 @ X13))),
% 0.46/0.64      inference('demod', [status(thm)], ['73', '74'])).
% 0.46/0.64  thf('76', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ X1))
% 0.46/0.64              = (k2_funct_1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['72', '75'])).
% 0.46/0.64  thf('77', plain,
% 0.46/0.64      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 0.46/0.64          = (k2_funct_1 @ sk_C))
% 0.46/0.64        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v1_relat_1 @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['71', '76'])).
% 0.46/0.64  thf('78', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('79', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('80', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['68', '69'])).
% 0.46/0.64  thf('81', plain,
% 0.46/0.64      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 0.46/0.64          = (k2_funct_1 @ sk_C))
% 0.46/0.64        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 0.46/0.64  thf('82', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 0.46/0.64            = (k2_funct_1 @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['60', '81'])).
% 0.46/0.64  thf('83', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['68', '69'])).
% 0.46/0.64  thf('84', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('85', plain,
% 0.46/0.64      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 0.46/0.64         = (k2_funct_1 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.46/0.64  thf('86', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['68', '69'])).
% 0.46/0.64  thf('87', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('88', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('89', plain, ((v1_relat_1 @ sk_D)),
% 0.46/0.64      inference('demod', [status(thm)], ['50', '51'])).
% 0.46/0.64  thf('90', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.46/0.64      inference('demod', [status(thm)],
% 0.46/0.64                ['37', '42', '59', '85', '86', '87', '88', '89'])).
% 0.46/0.64  thf('91', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('92', plain, ($false),
% 0.46/0.64      inference('simplify_reflect-', [status(thm)], ['90', '91'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
