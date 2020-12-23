%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WmcSH1nOe0

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:55 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  326 (1925 expanded)
%              Number of leaves         :   45 ( 602 expanded)
%              Depth                    :   39
%              Number of atoms          : 2755 (36618 expanded)
%              Number of equality atoms :  154 (2412 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( ( k1_partfun1 @ X41 @ X42 @ X44 @ X45 @ X40 @ X43 )
        = ( k5_relat_1 @ X40 @ X43 ) ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X39 ) ) ) ) ),
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

thf('19',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('21',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('22',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( X29 = X32 )
      | ~ ( r2_relset_1 @ X30 @ X31 @ X29 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','23'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('25',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('26',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('27',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','27'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('29',plain,(
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

thf('30',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X19 ) @ X19 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('31',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('32',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X19 ) @ X19 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X19 ) @ X19 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('34',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X19 ) @ X19 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('35',plain,(
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

thf('36',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('37',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
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
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('44',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['45'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('47',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ( v4_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['42','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('54',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('55',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['52','55','56','57'])).

thf('59',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['37','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('63',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['36','66'])).

thf('68',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('69',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['67','68','69','70','71','72'])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('74',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) ) @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ( v4_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ( v4_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v4_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','81'])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('84',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('85',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('91',plain,(
    v4_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['82','83','86','87','88','89','90'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('92',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5
        = ( k7_relat_1 @ X5 @ X6 ) )
      | ~ ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('93',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k7_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k7_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','93'])).

thf('95',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('96',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('97',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('98',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k7_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['94','95','96','97','98','99'])).

thf('101',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k7_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['32','100'])).

thf('102',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('103',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('104',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5
        = ( k7_relat_1 @ X5 @ X6 ) )
      | ~ ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k6_partfun1 @ X0 )
        = ( k7_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k6_partfun1 @ X0 )
      = ( k7_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('111',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['101','102','109','110','111','112'])).

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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) @ X11 )
        = ( k5_relat_1 @ X10 @ ( k5_relat_1 @ X9 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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
    inference('sup-',[status(thm)],['53','54'])).

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
    inference('sup-',[status(thm)],['29','117'])).

thf('119',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

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
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['28','121'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('123',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('124',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('125',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('127',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('129',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5
        = ( k7_relat_1 @ X5 @ X6 ) )
      | ~ ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('131',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('134',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['131','134'])).

thf('136',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('137',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('138',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('139',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) ) @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ( v4_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ( v4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( v4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['136','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( v4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['135','147'])).

thf('149',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['132','133'])).

thf('150',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['132','133'])).

thf('151',plain,(
    v4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('152',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5
        = ( k7_relat_1 @ X5 @ X6 ) )
      | ~ ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('153',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D ) )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k7_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k7_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['126','153'])).

thf('155',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['131','134'])).

thf('156',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['132','133'])).

thf('157',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['132','133'])).

thf('158',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k7_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D ) @ sk_B ) ),
    inference(demod,[status(thm)],['154','155','156','157'])).

thf('159',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k7_relat_1 @ ( k7_relat_1 @ sk_D @ sk_B ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['125','158'])).

thf('160',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['131','134'])).

thf('161',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['131','134'])).

thf('162',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['132','133'])).

thf('163',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['159','160','161','162'])).

thf('164',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['132','133'])).

thf('165',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['122','163','164'])).

thf('166',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('167',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('168',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) @ X11 )
        = ( k5_relat_1 @ X10 @ ( k5_relat_1 @ X9 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('169',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('171',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k5_relat_1 @ X1 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k1_relat_1 @ X18 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('174',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('175',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('176',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('177',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('178',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k7_relat_1 @ X16 @ X15 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('179',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('180',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('181',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['52','55','56','57'])).

thf('182',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5
        = ( k7_relat_1 @ X5 @ X6 ) )
      | ~ ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('183',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_funct_1 @ sk_C )
      = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['180','183'])).

thf('185',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('186',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['184','185','186'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('189',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,
    ( ( v4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) @ sk_B )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['179','190'])).

thf('192',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('193',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v4_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['191','192','193'])).

thf('195',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5
        = ( k7_relat_1 @ X5 @ X6 ) )
      | ~ ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('196',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k7_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k7_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['178','196'])).

thf('198',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['184','185','186'])).

thf('199',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k7_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k7_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k7_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['177','200'])).

thf('202',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('203',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k7_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['201','202','203'])).

thf('205',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['176','204'])).

thf('206',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['184','185','186'])).

thf('207',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['184','185','186'])).

thf('208',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['205','206','207'])).

thf('209',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['175','208'])).

thf('210',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('211',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['209','210','211'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('213',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ X14 @ ( k6_relat_1 @ ( k2_relat_1 @ X14 ) ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('214',plain,(
    ! [X46: $i] :
      ( ( k6_partfun1 @ X46 )
      = ( k6_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('215',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ X14 @ ( k6_partfun1 @ ( k2_relat_1 @ X14 ) ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) @ X11 )
        = ( k5_relat_1 @ X10 @ ( k5_relat_1 @ X9 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('219',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['217','218'])).

thf('220',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['212','219'])).

thf('221',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('222',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['209','210','211'])).

thf('223',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['209','210','211'])).

thf('224',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_funct_1 @ sk_C )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['220','221','222','223'])).

thf('225',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['224'])).

thf('226',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['174','225'])).

thf('227',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('228',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference(demod,[status(thm)],['226','227','228'])).

thf('230',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['173','229'])).

thf('231',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('232',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['230','231','232','233'])).

thf('235',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = ( k5_relat_1 @ ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['172','234'])).

thf('236',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['184','185','186'])).

thf('237',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('238',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['235','236','237'])).

thf('239',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['166','238'])).

thf('240',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('241',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['239','240','241'])).

thf('243',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['159','160','161','162'])).

thf('244',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['40','41'])).

thf('245',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ X14 @ ( k6_partfun1 @ ( k2_relat_1 @ X14 ) ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('246',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['244','245'])).

thf('247',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('248',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['246','247'])).

thf('249',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) @ X11 )
        = ( k5_relat_1 @ X10 @ ( k5_relat_1 @ X9 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('250',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['248','249'])).

thf('251',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('252',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('253',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['250','251','252'])).

thf('254',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) ) @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('255',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) ) @ ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['253','254'])).

thf('256',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('257',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) ) @ ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['255','256'])).

thf('258',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['243','257'])).

thf('259',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['132','133'])).

thf('260',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['132','133'])).

thf('261',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['258','259','260'])).

thf('262',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('263',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['261','262'])).

thf('264',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('265',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('266',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('268',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['266','267'])).

thf('269',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('270',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['268','269'])).

thf('271',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('272',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['270','271'])).

thf('273',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('274',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X12 ) )
      = X12 ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('275',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['263','264','265','272','273','274'])).

thf('276',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['242','275'])).

thf('277',plain,
    ( ( k2_funct_1 @ sk_C )
    = sk_D ),
    inference('sup+',[status(thm)],['165','276'])).

thf('278',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['277','278'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WmcSH1nOe0
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:52:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.60/1.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.60/1.80  % Solved by: fo/fo7.sh
% 1.60/1.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.60/1.80  % done 2075 iterations in 1.347s
% 1.60/1.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.60/1.80  % SZS output start Refutation
% 1.60/1.80  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.60/1.80  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.60/1.80  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.60/1.80  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.60/1.80  thf(sk_A_type, type, sk_A: $i).
% 1.60/1.80  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.60/1.80  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.60/1.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.60/1.80  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.60/1.80  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.60/1.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.60/1.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.60/1.80  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.60/1.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.60/1.80  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.60/1.80  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.60/1.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.60/1.80  thf(sk_D_type, type, sk_D: $i).
% 1.60/1.80  thf(sk_C_type, type, sk_C: $i).
% 1.60/1.80  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.60/1.80  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.60/1.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.60/1.80  thf(sk_B_type, type, sk_B: $i).
% 1.60/1.80  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.60/1.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.60/1.80  thf(t36_funct_2, conjecture,
% 1.60/1.80    (![A:$i,B:$i,C:$i]:
% 1.60/1.80     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.60/1.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.60/1.80       ( ![D:$i]:
% 1.60/1.80         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.60/1.80             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.60/1.80           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.60/1.80               ( r2_relset_1 @
% 1.60/1.80                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.60/1.80                 ( k6_partfun1 @ A ) ) & 
% 1.60/1.80               ( v2_funct_1 @ C ) ) =>
% 1.60/1.80             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.60/1.80               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.60/1.80  thf(zf_stmt_0, negated_conjecture,
% 1.60/1.80    (~( ![A:$i,B:$i,C:$i]:
% 1.60/1.80        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.60/1.80            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.60/1.80          ( ![D:$i]:
% 1.60/1.80            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.60/1.80                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.60/1.80              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.60/1.80                  ( r2_relset_1 @
% 1.60/1.80                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.60/1.80                    ( k6_partfun1 @ A ) ) & 
% 1.60/1.80                  ( v2_funct_1 @ C ) ) =>
% 1.60/1.80                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.60/1.80                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.60/1.80    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.60/1.80  thf('0', plain,
% 1.60/1.80      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.60/1.80        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.60/1.80        (k6_partfun1 @ sk_A))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('1', plain,
% 1.60/1.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('2', plain,
% 1.60/1.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf(redefinition_k1_partfun1, axiom,
% 1.60/1.80    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.60/1.80     ( ( ( v1_funct_1 @ E ) & 
% 1.60/1.80         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.60/1.80         ( v1_funct_1 @ F ) & 
% 1.60/1.80         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.60/1.80       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.60/1.80  thf('3', plain,
% 1.60/1.80      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 1.60/1.80         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 1.60/1.80          | ~ (v1_funct_1 @ X40)
% 1.60/1.80          | ~ (v1_funct_1 @ X43)
% 1.60/1.80          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 1.60/1.80          | ((k1_partfun1 @ X41 @ X42 @ X44 @ X45 @ X40 @ X43)
% 1.60/1.80              = (k5_relat_1 @ X40 @ X43)))),
% 1.60/1.80      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.60/1.80  thf('4', plain,
% 1.60/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.80         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.60/1.80            = (k5_relat_1 @ sk_C @ X0))
% 1.60/1.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.60/1.80          | ~ (v1_funct_1 @ X0)
% 1.60/1.80          | ~ (v1_funct_1 @ sk_C))),
% 1.60/1.80      inference('sup-', [status(thm)], ['2', '3'])).
% 1.60/1.80  thf('5', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('6', plain,
% 1.60/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.80         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.60/1.80            = (k5_relat_1 @ sk_C @ X0))
% 1.60/1.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.60/1.80          | ~ (v1_funct_1 @ X0))),
% 1.60/1.80      inference('demod', [status(thm)], ['4', '5'])).
% 1.60/1.80  thf('7', plain,
% 1.60/1.80      ((~ (v1_funct_1 @ sk_D)
% 1.60/1.80        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.60/1.80            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.60/1.80      inference('sup-', [status(thm)], ['1', '6'])).
% 1.60/1.80  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('9', plain,
% 1.60/1.80      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.60/1.80         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.60/1.80      inference('demod', [status(thm)], ['7', '8'])).
% 1.60/1.80  thf('10', plain,
% 1.60/1.80      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.60/1.80        (k6_partfun1 @ sk_A))),
% 1.60/1.80      inference('demod', [status(thm)], ['0', '9'])).
% 1.60/1.80  thf('11', plain,
% 1.60/1.80      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('12', plain,
% 1.60/1.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf(dt_k1_partfun1, axiom,
% 1.60/1.80    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.60/1.80     ( ( ( v1_funct_1 @ E ) & 
% 1.60/1.80         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.60/1.80         ( v1_funct_1 @ F ) & 
% 1.60/1.80         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.60/1.80       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.60/1.80         ( m1_subset_1 @
% 1.60/1.80           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.60/1.80           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.60/1.80  thf('13', plain,
% 1.60/1.80      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.60/1.80         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 1.60/1.80          | ~ (v1_funct_1 @ X34)
% 1.60/1.80          | ~ (v1_funct_1 @ X37)
% 1.60/1.80          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.60/1.80          | (m1_subset_1 @ (k1_partfun1 @ X35 @ X36 @ X38 @ X39 @ X34 @ X37) @ 
% 1.60/1.80             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X39))))),
% 1.60/1.80      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.60/1.80  thf('14', plain,
% 1.60/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.80         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.60/1.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.60/1.80          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.60/1.80          | ~ (v1_funct_1 @ X1)
% 1.60/1.80          | ~ (v1_funct_1 @ sk_C))),
% 1.60/1.80      inference('sup-', [status(thm)], ['12', '13'])).
% 1.60/1.80  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('16', plain,
% 1.60/1.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.80         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.60/1.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.60/1.80          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.60/1.80          | ~ (v1_funct_1 @ X1))),
% 1.60/1.80      inference('demod', [status(thm)], ['14', '15'])).
% 1.60/1.80  thf('17', plain,
% 1.60/1.80      ((~ (v1_funct_1 @ sk_D)
% 1.60/1.80        | (m1_subset_1 @ 
% 1.60/1.80           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.60/1.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.60/1.80      inference('sup-', [status(thm)], ['11', '16'])).
% 1.60/1.80  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('19', plain,
% 1.60/1.80      ((m1_subset_1 @ 
% 1.60/1.80        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.60/1.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.60/1.80      inference('demod', [status(thm)], ['17', '18'])).
% 1.60/1.80  thf('20', plain,
% 1.60/1.80      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.60/1.80         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.60/1.80      inference('demod', [status(thm)], ['7', '8'])).
% 1.60/1.80  thf('21', plain,
% 1.60/1.80      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.60/1.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.60/1.80      inference('demod', [status(thm)], ['19', '20'])).
% 1.60/1.80  thf(redefinition_r2_relset_1, axiom,
% 1.60/1.80    (![A:$i,B:$i,C:$i,D:$i]:
% 1.60/1.80     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.60/1.80         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.60/1.80       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.60/1.80  thf('22', plain,
% 1.60/1.80      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.60/1.80         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.60/1.80          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.60/1.80          | ((X29) = (X32))
% 1.60/1.80          | ~ (r2_relset_1 @ X30 @ X31 @ X29 @ X32))),
% 1.60/1.80      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.60/1.80  thf('23', plain,
% 1.60/1.80      (![X0 : $i]:
% 1.60/1.80         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.60/1.80          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.60/1.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.60/1.80      inference('sup-', [status(thm)], ['21', '22'])).
% 1.60/1.80  thf('24', plain,
% 1.60/1.80      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.60/1.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.60/1.80        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.60/1.80      inference('sup-', [status(thm)], ['10', '23'])).
% 1.60/1.80  thf(t29_relset_1, axiom,
% 1.60/1.80    (![A:$i]:
% 1.60/1.80     ( m1_subset_1 @
% 1.60/1.80       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.60/1.80  thf('25', plain,
% 1.60/1.80      (![X33 : $i]:
% 1.60/1.80         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 1.60/1.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 1.60/1.80      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.60/1.80  thf(redefinition_k6_partfun1, axiom,
% 1.60/1.80    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.60/1.80  thf('26', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 1.60/1.80      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.60/1.80  thf('27', plain,
% 1.60/1.80      (![X33 : $i]:
% 1.60/1.80         (m1_subset_1 @ (k6_partfun1 @ X33) @ 
% 1.60/1.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 1.60/1.80      inference('demod', [status(thm)], ['25', '26'])).
% 1.60/1.80  thf('28', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.60/1.80      inference('demod', [status(thm)], ['24', '27'])).
% 1.60/1.80  thf(dt_k2_funct_1, axiom,
% 1.60/1.80    (![A:$i]:
% 1.60/1.80     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.60/1.80       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.60/1.80         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.60/1.80  thf('29', plain,
% 1.60/1.80      (![X17 : $i]:
% 1.60/1.80         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 1.60/1.80          | ~ (v1_funct_1 @ X17)
% 1.60/1.80          | ~ (v1_relat_1 @ X17))),
% 1.60/1.80      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.80  thf(t61_funct_1, axiom,
% 1.60/1.80    (![A:$i]:
% 1.60/1.80     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.60/1.80       ( ( v2_funct_1 @ A ) =>
% 1.60/1.80         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.60/1.80             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.60/1.80           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.60/1.80             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.60/1.80  thf('30', plain,
% 1.60/1.80      (![X19 : $i]:
% 1.60/1.80         (~ (v2_funct_1 @ X19)
% 1.60/1.80          | ((k5_relat_1 @ (k2_funct_1 @ X19) @ X19)
% 1.60/1.80              = (k6_relat_1 @ (k2_relat_1 @ X19)))
% 1.60/1.80          | ~ (v1_funct_1 @ X19)
% 1.60/1.80          | ~ (v1_relat_1 @ X19))),
% 1.60/1.80      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.60/1.80  thf('31', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 1.60/1.80      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.60/1.80  thf('32', plain,
% 1.60/1.80      (![X19 : $i]:
% 1.60/1.80         (~ (v2_funct_1 @ X19)
% 1.60/1.80          | ((k5_relat_1 @ (k2_funct_1 @ X19) @ X19)
% 1.60/1.80              = (k6_partfun1 @ (k2_relat_1 @ X19)))
% 1.60/1.80          | ~ (v1_funct_1 @ X19)
% 1.60/1.80          | ~ (v1_relat_1 @ X19))),
% 1.60/1.80      inference('demod', [status(thm)], ['30', '31'])).
% 1.60/1.80  thf('33', plain,
% 1.60/1.80      (![X19 : $i]:
% 1.60/1.80         (~ (v2_funct_1 @ X19)
% 1.60/1.80          | ((k5_relat_1 @ (k2_funct_1 @ X19) @ X19)
% 1.60/1.80              = (k6_partfun1 @ (k2_relat_1 @ X19)))
% 1.60/1.80          | ~ (v1_funct_1 @ X19)
% 1.60/1.80          | ~ (v1_relat_1 @ X19))),
% 1.60/1.80      inference('demod', [status(thm)], ['30', '31'])).
% 1.60/1.80  thf('34', plain,
% 1.60/1.80      (![X19 : $i]:
% 1.60/1.80         (~ (v2_funct_1 @ X19)
% 1.60/1.80          | ((k5_relat_1 @ (k2_funct_1 @ X19) @ X19)
% 1.60/1.80              = (k6_partfun1 @ (k2_relat_1 @ X19)))
% 1.60/1.80          | ~ (v1_funct_1 @ X19)
% 1.60/1.80          | ~ (v1_relat_1 @ X19))),
% 1.60/1.80      inference('demod', [status(thm)], ['30', '31'])).
% 1.60/1.80  thf('35', plain,
% 1.60/1.80      (![X17 : $i]:
% 1.60/1.80         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 1.60/1.80          | ~ (v1_funct_1 @ X17)
% 1.60/1.80          | ~ (v1_relat_1 @ X17))),
% 1.60/1.80      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.80  thf(t55_funct_1, axiom,
% 1.60/1.80    (![A:$i]:
% 1.60/1.80     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.60/1.80       ( ( v2_funct_1 @ A ) =>
% 1.60/1.80         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.60/1.80           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.60/1.80  thf('36', plain,
% 1.60/1.80      (![X18 : $i]:
% 1.60/1.80         (~ (v2_funct_1 @ X18)
% 1.60/1.80          | ((k2_relat_1 @ X18) = (k1_relat_1 @ (k2_funct_1 @ X18)))
% 1.60/1.80          | ~ (v1_funct_1 @ X18)
% 1.60/1.80          | ~ (v1_relat_1 @ X18))),
% 1.60/1.80      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.60/1.80  thf('37', plain,
% 1.60/1.80      (![X17 : $i]:
% 1.60/1.80         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 1.60/1.80          | ~ (v1_funct_1 @ X17)
% 1.60/1.80          | ~ (v1_relat_1 @ X17))),
% 1.60/1.80      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.80  thf('38', plain,
% 1.60/1.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf(redefinition_k2_relset_1, axiom,
% 1.60/1.80    (![A:$i,B:$i,C:$i]:
% 1.60/1.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.60/1.80       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.60/1.80  thf('39', plain,
% 1.60/1.80      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.60/1.80         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 1.60/1.80          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.60/1.80      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.60/1.80  thf('40', plain,
% 1.60/1.80      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.60/1.80      inference('sup-', [status(thm)], ['38', '39'])).
% 1.60/1.80  thf('41', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('42', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.60/1.80      inference('sup+', [status(thm)], ['40', '41'])).
% 1.60/1.80  thf('43', plain,
% 1.60/1.80      (![X17 : $i]:
% 1.60/1.80         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 1.60/1.80          | ~ (v1_funct_1 @ X17)
% 1.60/1.80          | ~ (v1_relat_1 @ X17))),
% 1.60/1.80      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.80  thf('44', plain,
% 1.60/1.80      (![X18 : $i]:
% 1.60/1.80         (~ (v2_funct_1 @ X18)
% 1.60/1.80          | ((k2_relat_1 @ X18) = (k1_relat_1 @ (k2_funct_1 @ X18)))
% 1.60/1.80          | ~ (v1_funct_1 @ X18)
% 1.60/1.80          | ~ (v1_relat_1 @ X18))),
% 1.60/1.80      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.60/1.80  thf(d10_xboole_0, axiom,
% 1.60/1.80    (![A:$i,B:$i]:
% 1.60/1.80     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.60/1.80  thf('45', plain,
% 1.60/1.80      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.60/1.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.60/1.80  thf('46', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.60/1.80      inference('simplify', [status(thm)], ['45'])).
% 1.60/1.80  thf(d18_relat_1, axiom,
% 1.60/1.80    (![A:$i,B:$i]:
% 1.60/1.80     ( ( v1_relat_1 @ B ) =>
% 1.60/1.80       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.60/1.80  thf('47', plain,
% 1.60/1.80      (![X3 : $i, X4 : $i]:
% 1.60/1.80         (~ (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.60/1.80          | (v4_relat_1 @ X3 @ X4)
% 1.60/1.80          | ~ (v1_relat_1 @ X3))),
% 1.60/1.80      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.60/1.80  thf('48', plain,
% 1.60/1.80      (![X0 : $i]:
% 1.60/1.80         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 1.60/1.80      inference('sup-', [status(thm)], ['46', '47'])).
% 1.60/1.80  thf('49', plain,
% 1.60/1.80      (![X0 : $i]:
% 1.60/1.80         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.60/1.80          | ~ (v1_relat_1 @ X0)
% 1.60/1.80          | ~ (v1_funct_1 @ X0)
% 1.60/1.80          | ~ (v2_funct_1 @ X0)
% 1.60/1.80          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.60/1.80      inference('sup+', [status(thm)], ['44', '48'])).
% 1.60/1.80  thf('50', plain,
% 1.60/1.80      (![X0 : $i]:
% 1.60/1.80         (~ (v1_relat_1 @ X0)
% 1.60/1.80          | ~ (v1_funct_1 @ X0)
% 1.60/1.80          | ~ (v2_funct_1 @ X0)
% 1.60/1.80          | ~ (v1_funct_1 @ X0)
% 1.60/1.80          | ~ (v1_relat_1 @ X0)
% 1.60/1.80          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.60/1.80      inference('sup-', [status(thm)], ['43', '49'])).
% 1.60/1.80  thf('51', plain,
% 1.60/1.80      (![X0 : $i]:
% 1.60/1.80         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.60/1.80          | ~ (v2_funct_1 @ X0)
% 1.60/1.80          | ~ (v1_funct_1 @ X0)
% 1.60/1.80          | ~ (v1_relat_1 @ X0))),
% 1.60/1.80      inference('simplify', [status(thm)], ['50'])).
% 1.60/1.80  thf('52', plain,
% 1.60/1.80      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 1.60/1.80        | ~ (v1_relat_1 @ sk_C)
% 1.60/1.80        | ~ (v1_funct_1 @ sk_C)
% 1.60/1.80        | ~ (v2_funct_1 @ sk_C))),
% 1.60/1.80      inference('sup+', [status(thm)], ['42', '51'])).
% 1.60/1.80  thf('53', plain,
% 1.60/1.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf(cc1_relset_1, axiom,
% 1.60/1.80    (![A:$i,B:$i,C:$i]:
% 1.60/1.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.60/1.80       ( v1_relat_1 @ C ) ))).
% 1.60/1.80  thf('54', plain,
% 1.60/1.80      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.60/1.80         ((v1_relat_1 @ X20)
% 1.60/1.80          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.60/1.80      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.60/1.80  thf('55', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.80      inference('sup-', [status(thm)], ['53', '54'])).
% 1.60/1.80  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('57', plain, ((v2_funct_1 @ sk_C)),
% 1.60/1.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.80  thf('58', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 1.60/1.80      inference('demod', [status(thm)], ['52', '55', '56', '57'])).
% 1.60/1.80  thf('59', plain,
% 1.60/1.80      (![X3 : $i, X4 : $i]:
% 1.60/1.80         (~ (v4_relat_1 @ X3 @ X4)
% 1.60/1.80          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.60/1.80          | ~ (v1_relat_1 @ X3))),
% 1.60/1.80      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.60/1.80  thf('60', plain,
% 1.60/1.80      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.80        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.60/1.80      inference('sup-', [status(thm)], ['58', '59'])).
% 1.60/1.80  thf('61', plain,
% 1.60/1.80      ((~ (v1_relat_1 @ sk_C)
% 1.60/1.80        | ~ (v1_funct_1 @ sk_C)
% 1.60/1.80        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.60/1.80      inference('sup-', [status(thm)], ['37', '60'])).
% 1.60/1.80  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.81      inference('sup-', [status(thm)], ['53', '54'])).
% 1.60/1.81  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf('64', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 1.60/1.81      inference('demod', [status(thm)], ['61', '62', '63'])).
% 1.60/1.81  thf('65', plain,
% 1.60/1.81      (![X0 : $i, X2 : $i]:
% 1.60/1.81         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.60/1.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.60/1.81  thf('66', plain,
% 1.60/1.81      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.60/1.81        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.60/1.81      inference('sup-', [status(thm)], ['64', '65'])).
% 1.60/1.81  thf('67', plain,
% 1.60/1.81      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 1.60/1.81        | ~ (v1_relat_1 @ sk_C)
% 1.60/1.81        | ~ (v1_funct_1 @ sk_C)
% 1.60/1.81        | ~ (v2_funct_1 @ sk_C)
% 1.60/1.81        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.60/1.81      inference('sup-', [status(thm)], ['36', '66'])).
% 1.60/1.81  thf('68', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.60/1.81      inference('sup+', [status(thm)], ['40', '41'])).
% 1.60/1.81  thf('69', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.60/1.81      inference('simplify', [status(thm)], ['45'])).
% 1.60/1.81  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.81      inference('sup-', [status(thm)], ['53', '54'])).
% 1.60/1.81  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf('72', plain, ((v2_funct_1 @ sk_C)),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf('73', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.60/1.81      inference('demod', [status(thm)], ['67', '68', '69', '70', '71', '72'])).
% 1.60/1.81  thf(t44_relat_1, axiom,
% 1.60/1.81    (![A:$i]:
% 1.60/1.81     ( ( v1_relat_1 @ A ) =>
% 1.60/1.81       ( ![B:$i]:
% 1.60/1.81         ( ( v1_relat_1 @ B ) =>
% 1.60/1.81           ( r1_tarski @
% 1.60/1.81             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 1.60/1.81  thf('74', plain,
% 1.60/1.81      (![X7 : $i, X8 : $i]:
% 1.60/1.81         (~ (v1_relat_1 @ X7)
% 1.60/1.81          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X8 @ X7)) @ 
% 1.60/1.81             (k1_relat_1 @ X8))
% 1.60/1.81          | ~ (v1_relat_1 @ X8))),
% 1.60/1.81      inference('cnf', [status(esa)], [t44_relat_1])).
% 1.60/1.81  thf('75', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         ((r1_tarski @ 
% 1.60/1.81           (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)) @ sk_B)
% 1.60/1.81          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.81          | ~ (v1_relat_1 @ X0))),
% 1.60/1.81      inference('sup+', [status(thm)], ['73', '74'])).
% 1.60/1.81  thf('76', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         (~ (v1_relat_1 @ sk_C)
% 1.60/1.81          | ~ (v1_funct_1 @ sk_C)
% 1.60/1.81          | ~ (v1_relat_1 @ X0)
% 1.60/1.81          | (r1_tarski @ 
% 1.60/1.81             (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)) @ sk_B))),
% 1.60/1.81      inference('sup-', [status(thm)], ['35', '75'])).
% 1.60/1.81  thf('77', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.81      inference('sup-', [status(thm)], ['53', '54'])).
% 1.60/1.81  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf('79', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         (~ (v1_relat_1 @ X0)
% 1.60/1.81          | (r1_tarski @ 
% 1.60/1.81             (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)) @ sk_B))),
% 1.60/1.81      inference('demod', [status(thm)], ['76', '77', '78'])).
% 1.60/1.81  thf('80', plain,
% 1.60/1.81      (![X3 : $i, X4 : $i]:
% 1.60/1.81         (~ (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.60/1.81          | (v4_relat_1 @ X3 @ X4)
% 1.60/1.81          | ~ (v1_relat_1 @ X3))),
% 1.60/1.81      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.60/1.81  thf('81', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         (~ (v1_relat_1 @ X0)
% 1.60/1.81          | ~ (v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))
% 1.60/1.81          | (v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0) @ sk_B))),
% 1.60/1.81      inference('sup-', [status(thm)], ['79', '80'])).
% 1.60/1.81  thf('82', plain,
% 1.60/1.81      ((~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.60/1.81        | ~ (v1_relat_1 @ sk_C)
% 1.60/1.81        | ~ (v1_funct_1 @ sk_C)
% 1.60/1.81        | ~ (v2_funct_1 @ sk_C)
% 1.60/1.81        | (v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) @ sk_B)
% 1.60/1.81        | ~ (v1_relat_1 @ sk_C))),
% 1.60/1.81      inference('sup-', [status(thm)], ['34', '81'])).
% 1.60/1.81  thf('83', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.60/1.81      inference('sup+', [status(thm)], ['40', '41'])).
% 1.60/1.81  thf('84', plain,
% 1.60/1.81      (![X33 : $i]:
% 1.60/1.81         (m1_subset_1 @ (k6_partfun1 @ X33) @ 
% 1.60/1.81          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 1.60/1.81      inference('demod', [status(thm)], ['25', '26'])).
% 1.60/1.81  thf('85', plain,
% 1.60/1.81      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.60/1.81         ((v1_relat_1 @ X20)
% 1.60/1.81          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.60/1.81      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.60/1.81  thf('86', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.60/1.81      inference('sup-', [status(thm)], ['84', '85'])).
% 1.60/1.81  thf('87', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.81      inference('sup-', [status(thm)], ['53', '54'])).
% 1.60/1.81  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf('89', plain, ((v2_funct_1 @ sk_C)),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf('90', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.81      inference('sup-', [status(thm)], ['53', '54'])).
% 1.60/1.81  thf('91', plain,
% 1.60/1.81      ((v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) @ sk_B)),
% 1.60/1.81      inference('demod', [status(thm)],
% 1.60/1.81                ['82', '83', '86', '87', '88', '89', '90'])).
% 1.60/1.81  thf(t209_relat_1, axiom,
% 1.60/1.81    (![A:$i,B:$i]:
% 1.60/1.81     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.60/1.81       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.60/1.81  thf('92', plain,
% 1.60/1.81      (![X5 : $i, X6 : $i]:
% 1.60/1.81         (((X5) = (k7_relat_1 @ X5 @ X6))
% 1.60/1.81          | ~ (v4_relat_1 @ X5 @ X6)
% 1.60/1.81          | ~ (v1_relat_1 @ X5))),
% 1.60/1.81      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.60/1.81  thf('93', plain,
% 1.60/1.81      ((~ (v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.60/1.81        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 1.60/1.81            = (k7_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) @ sk_B)))),
% 1.60/1.81      inference('sup-', [status(thm)], ['91', '92'])).
% 1.60/1.81  thf('94', plain,
% 1.60/1.81      ((~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.60/1.81        | ~ (v1_relat_1 @ sk_C)
% 1.60/1.81        | ~ (v1_funct_1 @ sk_C)
% 1.60/1.81        | ~ (v2_funct_1 @ sk_C)
% 1.60/1.81        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 1.60/1.81            = (k7_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) @ sk_B)))),
% 1.60/1.81      inference('sup-', [status(thm)], ['33', '93'])).
% 1.60/1.81  thf('95', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.60/1.81      inference('sup+', [status(thm)], ['40', '41'])).
% 1.60/1.81  thf('96', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.60/1.81      inference('sup-', [status(thm)], ['84', '85'])).
% 1.60/1.81  thf('97', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.81      inference('sup-', [status(thm)], ['53', '54'])).
% 1.60/1.81  thf('98', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf('99', plain, ((v2_funct_1 @ sk_C)),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf('100', plain,
% 1.60/1.81      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 1.60/1.81         = (k7_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) @ sk_B))),
% 1.60/1.81      inference('demod', [status(thm)], ['94', '95', '96', '97', '98', '99'])).
% 1.60/1.81  thf('101', plain,
% 1.60/1.81      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 1.60/1.81          = (k7_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ sk_B))
% 1.60/1.81        | ~ (v1_relat_1 @ sk_C)
% 1.60/1.81        | ~ (v1_funct_1 @ sk_C)
% 1.60/1.81        | ~ (v2_funct_1 @ sk_C))),
% 1.60/1.81      inference('sup+', [status(thm)], ['32', '100'])).
% 1.60/1.81  thf('102', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.60/1.81      inference('sup+', [status(thm)], ['40', '41'])).
% 1.60/1.81  thf('103', plain,
% 1.60/1.81      (![X33 : $i]:
% 1.60/1.81         (m1_subset_1 @ (k6_partfun1 @ X33) @ 
% 1.60/1.81          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 1.60/1.81      inference('demod', [status(thm)], ['25', '26'])).
% 1.60/1.81  thf(cc2_relset_1, axiom,
% 1.60/1.81    (![A:$i,B:$i,C:$i]:
% 1.60/1.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.60/1.81       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.60/1.81  thf('104', plain,
% 1.60/1.81      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.60/1.81         ((v4_relat_1 @ X23 @ X24)
% 1.60/1.81          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.60/1.81      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.60/1.81  thf('105', plain, (![X0 : $i]: (v4_relat_1 @ (k6_partfun1 @ X0) @ X0)),
% 1.60/1.81      inference('sup-', [status(thm)], ['103', '104'])).
% 1.60/1.81  thf('106', plain,
% 1.60/1.81      (![X5 : $i, X6 : $i]:
% 1.60/1.81         (((X5) = (k7_relat_1 @ X5 @ X6))
% 1.60/1.81          | ~ (v4_relat_1 @ X5 @ X6)
% 1.60/1.81          | ~ (v1_relat_1 @ X5))),
% 1.60/1.81      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.60/1.81  thf('107', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.60/1.81          | ((k6_partfun1 @ X0) = (k7_relat_1 @ (k6_partfun1 @ X0) @ X0)))),
% 1.60/1.81      inference('sup-', [status(thm)], ['105', '106'])).
% 1.60/1.81  thf('108', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.60/1.81      inference('sup-', [status(thm)], ['84', '85'])).
% 1.60/1.81  thf('109', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         ((k6_partfun1 @ X0) = (k7_relat_1 @ (k6_partfun1 @ X0) @ X0))),
% 1.60/1.81      inference('demod', [status(thm)], ['107', '108'])).
% 1.60/1.81  thf('110', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.81      inference('sup-', [status(thm)], ['53', '54'])).
% 1.60/1.81  thf('111', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf('112', plain, ((v2_funct_1 @ sk_C)),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf('113', plain,
% 1.60/1.81      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 1.60/1.81      inference('demod', [status(thm)],
% 1.60/1.81                ['101', '102', '109', '110', '111', '112'])).
% 1.60/1.81  thf(t55_relat_1, axiom,
% 1.60/1.81    (![A:$i]:
% 1.60/1.81     ( ( v1_relat_1 @ A ) =>
% 1.60/1.81       ( ![B:$i]:
% 1.60/1.81         ( ( v1_relat_1 @ B ) =>
% 1.60/1.81           ( ![C:$i]:
% 1.60/1.81             ( ( v1_relat_1 @ C ) =>
% 1.60/1.81               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.60/1.81                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.60/1.81  thf('114', plain,
% 1.60/1.81      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.60/1.81         (~ (v1_relat_1 @ X9)
% 1.60/1.81          | ((k5_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 1.60/1.81              = (k5_relat_1 @ X10 @ (k5_relat_1 @ X9 @ X11)))
% 1.60/1.81          | ~ (v1_relat_1 @ X11)
% 1.60/1.81          | ~ (v1_relat_1 @ X10))),
% 1.60/1.81      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.60/1.81  thf('115', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.60/1.81            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.60/1.81          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.81          | ~ (v1_relat_1 @ X0)
% 1.60/1.81          | ~ (v1_relat_1 @ sk_C))),
% 1.60/1.81      inference('sup+', [status(thm)], ['113', '114'])).
% 1.60/1.81  thf('116', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.81      inference('sup-', [status(thm)], ['53', '54'])).
% 1.60/1.81  thf('117', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.60/1.81            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.60/1.81          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.81          | ~ (v1_relat_1 @ X0))),
% 1.60/1.81      inference('demod', [status(thm)], ['115', '116'])).
% 1.60/1.81  thf('118', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         (~ (v1_relat_1 @ sk_C)
% 1.60/1.81          | ~ (v1_funct_1 @ sk_C)
% 1.60/1.81          | ~ (v1_relat_1 @ X0)
% 1.60/1.81          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.60/1.81              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.60/1.81      inference('sup-', [status(thm)], ['29', '117'])).
% 1.60/1.81  thf('119', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.81      inference('sup-', [status(thm)], ['53', '54'])).
% 1.60/1.81  thf('120', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf('121', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         (~ (v1_relat_1 @ X0)
% 1.60/1.81          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.60/1.81              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.60/1.81      inference('demod', [status(thm)], ['118', '119', '120'])).
% 1.60/1.81  thf('122', plain,
% 1.60/1.81      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.60/1.81          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 1.60/1.81        | ~ (v1_relat_1 @ sk_D))),
% 1.60/1.81      inference('sup+', [status(thm)], ['28', '121'])).
% 1.60/1.81  thf(t94_relat_1, axiom,
% 1.60/1.81    (![A:$i,B:$i]:
% 1.60/1.81     ( ( v1_relat_1 @ B ) =>
% 1.60/1.81       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 1.60/1.81  thf('123', plain,
% 1.60/1.81      (![X15 : $i, X16 : $i]:
% 1.60/1.81         (((k7_relat_1 @ X16 @ X15) = (k5_relat_1 @ (k6_relat_1 @ X15) @ X16))
% 1.60/1.81          | ~ (v1_relat_1 @ X16))),
% 1.60/1.81      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.60/1.81  thf('124', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 1.60/1.81      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.60/1.81  thf('125', plain,
% 1.60/1.81      (![X15 : $i, X16 : $i]:
% 1.60/1.81         (((k7_relat_1 @ X16 @ X15) = (k5_relat_1 @ (k6_partfun1 @ X15) @ X16))
% 1.60/1.81          | ~ (v1_relat_1 @ X16))),
% 1.60/1.81      inference('demod', [status(thm)], ['123', '124'])).
% 1.60/1.81  thf('126', plain,
% 1.60/1.81      (![X15 : $i, X16 : $i]:
% 1.60/1.81         (((k7_relat_1 @ X16 @ X15) = (k5_relat_1 @ (k6_partfun1 @ X15) @ X16))
% 1.60/1.81          | ~ (v1_relat_1 @ X16))),
% 1.60/1.81      inference('demod', [status(thm)], ['123', '124'])).
% 1.60/1.81  thf('127', plain,
% 1.60/1.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf('128', plain,
% 1.60/1.81      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.60/1.81         ((v4_relat_1 @ X23 @ X24)
% 1.60/1.81          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.60/1.81      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.60/1.81  thf('129', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 1.60/1.81      inference('sup-', [status(thm)], ['127', '128'])).
% 1.60/1.81  thf('130', plain,
% 1.60/1.81      (![X5 : $i, X6 : $i]:
% 1.60/1.81         (((X5) = (k7_relat_1 @ X5 @ X6))
% 1.60/1.81          | ~ (v4_relat_1 @ X5 @ X6)
% 1.60/1.81          | ~ (v1_relat_1 @ X5))),
% 1.60/1.81      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.60/1.81  thf('131', plain,
% 1.60/1.81      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_B)))),
% 1.60/1.81      inference('sup-', [status(thm)], ['129', '130'])).
% 1.60/1.81  thf('132', plain,
% 1.60/1.81      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf('133', plain,
% 1.60/1.81      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.60/1.81         ((v1_relat_1 @ X20)
% 1.60/1.81          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.60/1.81      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.60/1.81  thf('134', plain, ((v1_relat_1 @ sk_D)),
% 1.60/1.81      inference('sup-', [status(thm)], ['132', '133'])).
% 1.60/1.81  thf('135', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 1.60/1.81      inference('demod', [status(thm)], ['131', '134'])).
% 1.60/1.81  thf('136', plain,
% 1.60/1.81      (![X15 : $i, X16 : $i]:
% 1.60/1.81         (((k7_relat_1 @ X16 @ X15) = (k5_relat_1 @ (k6_partfun1 @ X15) @ X16))
% 1.60/1.81          | ~ (v1_relat_1 @ X16))),
% 1.60/1.81      inference('demod', [status(thm)], ['123', '124'])).
% 1.60/1.81  thf(t71_relat_1, axiom,
% 1.60/1.81    (![A:$i]:
% 1.60/1.81     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.60/1.81       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.60/1.81  thf('137', plain, (![X12 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 1.60/1.81      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.60/1.81  thf('138', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 1.60/1.81      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.60/1.81  thf('139', plain,
% 1.60/1.81      (![X12 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X12)) = (X12))),
% 1.60/1.81      inference('demod', [status(thm)], ['137', '138'])).
% 1.60/1.81  thf('140', plain,
% 1.60/1.81      (![X7 : $i, X8 : $i]:
% 1.60/1.81         (~ (v1_relat_1 @ X7)
% 1.60/1.81          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X8 @ X7)) @ 
% 1.60/1.81             (k1_relat_1 @ X8))
% 1.60/1.81          | ~ (v1_relat_1 @ X8))),
% 1.60/1.81      inference('cnf', [status(esa)], [t44_relat_1])).
% 1.60/1.81  thf('141', plain,
% 1.60/1.81      (![X0 : $i, X1 : $i]:
% 1.60/1.81         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1)) @ 
% 1.60/1.81           X0)
% 1.60/1.81          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.60/1.81          | ~ (v1_relat_1 @ X1))),
% 1.60/1.81      inference('sup+', [status(thm)], ['139', '140'])).
% 1.60/1.81  thf('142', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.60/1.81      inference('sup-', [status(thm)], ['84', '85'])).
% 1.60/1.81  thf('143', plain,
% 1.60/1.81      (![X0 : $i, X1 : $i]:
% 1.60/1.81         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1)) @ 
% 1.60/1.81           X0)
% 1.60/1.81          | ~ (v1_relat_1 @ X1))),
% 1.60/1.81      inference('demod', [status(thm)], ['141', '142'])).
% 1.60/1.81  thf('144', plain,
% 1.60/1.81      (![X3 : $i, X4 : $i]:
% 1.60/1.81         (~ (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.60/1.81          | (v4_relat_1 @ X3 @ X4)
% 1.60/1.81          | ~ (v1_relat_1 @ X3))),
% 1.60/1.81      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.60/1.81  thf('145', plain,
% 1.60/1.81      (![X0 : $i, X1 : $i]:
% 1.60/1.81         (~ (v1_relat_1 @ X1)
% 1.60/1.81          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 1.60/1.81          | (v4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1) @ X0))),
% 1.60/1.81      inference('sup-', [status(thm)], ['143', '144'])).
% 1.60/1.81  thf('146', plain,
% 1.60/1.81      (![X0 : $i, X1 : $i]:
% 1.60/1.81         (~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 1.60/1.81          | ~ (v1_relat_1 @ X1)
% 1.60/1.81          | (v4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1) @ X0)
% 1.60/1.81          | ~ (v1_relat_1 @ X1))),
% 1.60/1.81      inference('sup-', [status(thm)], ['136', '145'])).
% 1.60/1.81  thf('147', plain,
% 1.60/1.81      (![X0 : $i, X1 : $i]:
% 1.60/1.81         ((v4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1) @ X0)
% 1.60/1.81          | ~ (v1_relat_1 @ X1)
% 1.60/1.81          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.60/1.81      inference('simplify', [status(thm)], ['146'])).
% 1.60/1.81  thf('148', plain,
% 1.60/1.81      ((~ (v1_relat_1 @ sk_D)
% 1.60/1.81        | ~ (v1_relat_1 @ sk_D)
% 1.60/1.81        | (v4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) @ sk_B))),
% 1.60/1.81      inference('sup-', [status(thm)], ['135', '147'])).
% 1.60/1.81  thf('149', plain, ((v1_relat_1 @ sk_D)),
% 1.60/1.81      inference('sup-', [status(thm)], ['132', '133'])).
% 1.60/1.81  thf('150', plain, ((v1_relat_1 @ sk_D)),
% 1.60/1.81      inference('sup-', [status(thm)], ['132', '133'])).
% 1.60/1.81  thf('151', plain,
% 1.60/1.81      ((v4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) @ sk_B)),
% 1.60/1.81      inference('demod', [status(thm)], ['148', '149', '150'])).
% 1.60/1.81  thf('152', plain,
% 1.60/1.81      (![X5 : $i, X6 : $i]:
% 1.60/1.81         (((X5) = (k7_relat_1 @ X5 @ X6))
% 1.60/1.81          | ~ (v4_relat_1 @ X5 @ X6)
% 1.60/1.81          | ~ (v1_relat_1 @ X5))),
% 1.60/1.81      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.60/1.81  thf('153', plain,
% 1.60/1.81      ((~ (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D))
% 1.60/1.81        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.60/1.81            = (k7_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) @ sk_B)))),
% 1.60/1.81      inference('sup-', [status(thm)], ['151', '152'])).
% 1.60/1.81  thf('154', plain,
% 1.60/1.81      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ sk_B))
% 1.60/1.81        | ~ (v1_relat_1 @ sk_D)
% 1.60/1.81        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.60/1.81            = (k7_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) @ sk_B)))),
% 1.60/1.81      inference('sup-', [status(thm)], ['126', '153'])).
% 1.60/1.81  thf('155', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 1.60/1.81      inference('demod', [status(thm)], ['131', '134'])).
% 1.60/1.81  thf('156', plain, ((v1_relat_1 @ sk_D)),
% 1.60/1.81      inference('sup-', [status(thm)], ['132', '133'])).
% 1.60/1.81  thf('157', plain, ((v1_relat_1 @ sk_D)),
% 1.60/1.81      inference('sup-', [status(thm)], ['132', '133'])).
% 1.60/1.81  thf('158', plain,
% 1.60/1.81      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.60/1.81         = (k7_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) @ sk_B))),
% 1.60/1.81      inference('demod', [status(thm)], ['154', '155', '156', '157'])).
% 1.60/1.81  thf('159', plain,
% 1.60/1.81      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 1.60/1.81          = (k7_relat_1 @ (k7_relat_1 @ sk_D @ sk_B) @ sk_B))
% 1.60/1.81        | ~ (v1_relat_1 @ sk_D))),
% 1.60/1.81      inference('sup+', [status(thm)], ['125', '158'])).
% 1.60/1.81  thf('160', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 1.60/1.81      inference('demod', [status(thm)], ['131', '134'])).
% 1.60/1.81  thf('161', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 1.60/1.81      inference('demod', [status(thm)], ['131', '134'])).
% 1.60/1.81  thf('162', plain, ((v1_relat_1 @ sk_D)),
% 1.60/1.81      inference('sup-', [status(thm)], ['132', '133'])).
% 1.60/1.81  thf('163', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 1.60/1.81      inference('demod', [status(thm)], ['159', '160', '161', '162'])).
% 1.60/1.81  thf('164', plain, ((v1_relat_1 @ sk_D)),
% 1.60/1.81      inference('sup-', [status(thm)], ['132', '133'])).
% 1.60/1.81  thf('165', plain,
% 1.60/1.81      (((sk_D) = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))),
% 1.60/1.81      inference('demod', [status(thm)], ['122', '163', '164'])).
% 1.60/1.81  thf('166', plain,
% 1.60/1.81      (![X17 : $i]:
% 1.60/1.81         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 1.60/1.81          | ~ (v1_funct_1 @ X17)
% 1.60/1.81          | ~ (v1_relat_1 @ X17))),
% 1.60/1.81      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.81  thf('167', plain,
% 1.60/1.81      (![X15 : $i, X16 : $i]:
% 1.60/1.81         (((k7_relat_1 @ X16 @ X15) = (k5_relat_1 @ (k6_partfun1 @ X15) @ X16))
% 1.60/1.81          | ~ (v1_relat_1 @ X16))),
% 1.60/1.81      inference('demod', [status(thm)], ['123', '124'])).
% 1.60/1.81  thf('168', plain,
% 1.60/1.81      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.60/1.81         (~ (v1_relat_1 @ X9)
% 1.60/1.81          | ((k5_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 1.60/1.81              = (k5_relat_1 @ X10 @ (k5_relat_1 @ X9 @ X11)))
% 1.60/1.81          | ~ (v1_relat_1 @ X11)
% 1.60/1.81          | ~ (v1_relat_1 @ X10))),
% 1.60/1.81      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.60/1.81  thf('169', plain,
% 1.60/1.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.81         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.60/1.81            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 1.60/1.81          | ~ (v1_relat_1 @ X1)
% 1.60/1.81          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 1.60/1.81          | ~ (v1_relat_1 @ X2)
% 1.60/1.81          | ~ (v1_relat_1 @ X1))),
% 1.60/1.81      inference('sup+', [status(thm)], ['167', '168'])).
% 1.60/1.81  thf('170', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.60/1.81      inference('sup-', [status(thm)], ['84', '85'])).
% 1.60/1.81  thf('171', plain,
% 1.60/1.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.81         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.60/1.81            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k5_relat_1 @ X1 @ X2)))
% 1.60/1.81          | ~ (v1_relat_1 @ X1)
% 1.60/1.81          | ~ (v1_relat_1 @ X2)
% 1.60/1.81          | ~ (v1_relat_1 @ X1))),
% 1.60/1.81      inference('demod', [status(thm)], ['169', '170'])).
% 1.60/1.81  thf('172', plain,
% 1.60/1.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.81         (~ (v1_relat_1 @ X2)
% 1.60/1.81          | ~ (v1_relat_1 @ X1)
% 1.60/1.81          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 1.60/1.81              = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k5_relat_1 @ X1 @ X2))))),
% 1.60/1.81      inference('simplify', [status(thm)], ['171'])).
% 1.60/1.81  thf('173', plain,
% 1.60/1.81      (![X18 : $i]:
% 1.60/1.81         (~ (v2_funct_1 @ X18)
% 1.60/1.81          | ((k1_relat_1 @ X18) = (k2_relat_1 @ (k2_funct_1 @ X18)))
% 1.60/1.81          | ~ (v1_funct_1 @ X18)
% 1.60/1.81          | ~ (v1_relat_1 @ X18))),
% 1.60/1.81      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.60/1.81  thf('174', plain,
% 1.60/1.81      (![X17 : $i]:
% 1.60/1.81         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 1.60/1.81          | ~ (v1_funct_1 @ X17)
% 1.60/1.81          | ~ (v1_relat_1 @ X17))),
% 1.60/1.81      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.81  thf('175', plain,
% 1.60/1.81      (![X17 : $i]:
% 1.60/1.81         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 1.60/1.81          | ~ (v1_funct_1 @ X17)
% 1.60/1.81          | ~ (v1_relat_1 @ X17))),
% 1.60/1.81      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.81  thf('176', plain,
% 1.60/1.81      (![X15 : $i, X16 : $i]:
% 1.60/1.81         (((k7_relat_1 @ X16 @ X15) = (k5_relat_1 @ (k6_partfun1 @ X15) @ X16))
% 1.60/1.81          | ~ (v1_relat_1 @ X16))),
% 1.60/1.81      inference('demod', [status(thm)], ['123', '124'])).
% 1.60/1.81  thf('177', plain,
% 1.60/1.81      (![X17 : $i]:
% 1.60/1.81         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 1.60/1.81          | ~ (v1_funct_1 @ X17)
% 1.60/1.81          | ~ (v1_relat_1 @ X17))),
% 1.60/1.81      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.81  thf('178', plain,
% 1.60/1.81      (![X15 : $i, X16 : $i]:
% 1.60/1.81         (((k7_relat_1 @ X16 @ X15) = (k5_relat_1 @ (k6_partfun1 @ X15) @ X16))
% 1.60/1.81          | ~ (v1_relat_1 @ X16))),
% 1.60/1.81      inference('demod', [status(thm)], ['123', '124'])).
% 1.60/1.81  thf('179', plain,
% 1.60/1.81      (![X17 : $i]:
% 1.60/1.81         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 1.60/1.81          | ~ (v1_funct_1 @ X17)
% 1.60/1.81          | ~ (v1_relat_1 @ X17))),
% 1.60/1.81      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.81  thf('180', plain,
% 1.60/1.81      (![X17 : $i]:
% 1.60/1.81         ((v1_relat_1 @ (k2_funct_1 @ X17))
% 1.60/1.81          | ~ (v1_funct_1 @ X17)
% 1.60/1.81          | ~ (v1_relat_1 @ X17))),
% 1.60/1.81      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.60/1.81  thf('181', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 1.60/1.81      inference('demod', [status(thm)], ['52', '55', '56', '57'])).
% 1.60/1.81  thf('182', plain,
% 1.60/1.81      (![X5 : $i, X6 : $i]:
% 1.60/1.81         (((X5) = (k7_relat_1 @ X5 @ X6))
% 1.60/1.81          | ~ (v4_relat_1 @ X5 @ X6)
% 1.60/1.81          | ~ (v1_relat_1 @ X5))),
% 1.60/1.81      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.60/1.81  thf('183', plain,
% 1.60/1.81      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.81        | ((k2_funct_1 @ sk_C) = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)))),
% 1.60/1.81      inference('sup-', [status(thm)], ['181', '182'])).
% 1.60/1.81  thf('184', plain,
% 1.60/1.81      ((~ (v1_relat_1 @ sk_C)
% 1.60/1.81        | ~ (v1_funct_1 @ sk_C)
% 1.60/1.81        | ((k2_funct_1 @ sk_C) = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)))),
% 1.60/1.81      inference('sup-', [status(thm)], ['180', '183'])).
% 1.60/1.81  thf('185', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.81      inference('sup-', [status(thm)], ['53', '54'])).
% 1.60/1.81  thf('186', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf('187', plain,
% 1.60/1.81      (((k2_funct_1 @ sk_C) = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B))),
% 1.60/1.81      inference('demod', [status(thm)], ['184', '185', '186'])).
% 1.60/1.81  thf('188', plain,
% 1.60/1.81      (![X0 : $i, X1 : $i]:
% 1.60/1.81         ((v4_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1) @ X0)
% 1.60/1.81          | ~ (v1_relat_1 @ X1)
% 1.60/1.81          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 1.60/1.81      inference('simplify', [status(thm)], ['146'])).
% 1.60/1.81  thf('189', plain,
% 1.60/1.81      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.81        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.81        | (v4_relat_1 @ 
% 1.60/1.81           (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.60/1.81      inference('sup-', [status(thm)], ['187', '188'])).
% 1.60/1.81  thf('190', plain,
% 1.60/1.81      (((v4_relat_1 @ 
% 1.60/1.81         (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)) @ sk_B)
% 1.60/1.81        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.60/1.81      inference('simplify', [status(thm)], ['189'])).
% 1.60/1.81  thf('191', plain,
% 1.60/1.81      ((~ (v1_relat_1 @ sk_C)
% 1.60/1.81        | ~ (v1_funct_1 @ sk_C)
% 1.60/1.81        | (v4_relat_1 @ 
% 1.60/1.81           (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.60/1.81      inference('sup-', [status(thm)], ['179', '190'])).
% 1.60/1.81  thf('192', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.81      inference('sup-', [status(thm)], ['53', '54'])).
% 1.60/1.81  thf('193', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf('194', plain,
% 1.60/1.81      ((v4_relat_1 @ 
% 1.60/1.81        (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 1.60/1.81      inference('demod', [status(thm)], ['191', '192', '193'])).
% 1.60/1.81  thf('195', plain,
% 1.60/1.81      (![X5 : $i, X6 : $i]:
% 1.60/1.81         (((X5) = (k7_relat_1 @ X5 @ X6))
% 1.60/1.81          | ~ (v4_relat_1 @ X5 @ X6)
% 1.60/1.81          | ~ (v1_relat_1 @ X5))),
% 1.60/1.81      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.60/1.81  thf('196', plain,
% 1.60/1.81      ((~ (v1_relat_1 @ 
% 1.60/1.81           (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)))
% 1.60/1.81        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.60/1.81            = (k7_relat_1 @ 
% 1.60/1.81               (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)) @ sk_B)))),
% 1.60/1.81      inference('sup-', [status(thm)], ['194', '195'])).
% 1.60/1.81  thf('197', plain,
% 1.60/1.81      ((~ (v1_relat_1 @ (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B))
% 1.60/1.81        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.81        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.60/1.81            = (k7_relat_1 @ 
% 1.60/1.81               (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)) @ sk_B)))),
% 1.60/1.81      inference('sup-', [status(thm)], ['178', '196'])).
% 1.60/1.81  thf('198', plain,
% 1.60/1.81      (((k2_funct_1 @ sk_C) = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B))),
% 1.60/1.81      inference('demod', [status(thm)], ['184', '185', '186'])).
% 1.60/1.81  thf('199', plain,
% 1.60/1.81      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.81        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.81        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.60/1.81            = (k7_relat_1 @ 
% 1.60/1.81               (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)) @ sk_B)))),
% 1.60/1.81      inference('demod', [status(thm)], ['197', '198'])).
% 1.60/1.81  thf('200', plain,
% 1.60/1.81      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.60/1.81          = (k7_relat_1 @ 
% 1.60/1.81             (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)) @ sk_B))
% 1.60/1.81        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.60/1.81      inference('simplify', [status(thm)], ['199'])).
% 1.60/1.81  thf('201', plain,
% 1.60/1.81      ((~ (v1_relat_1 @ sk_C)
% 1.60/1.81        | ~ (v1_funct_1 @ sk_C)
% 1.60/1.81        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.60/1.81            = (k7_relat_1 @ 
% 1.60/1.81               (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)) @ sk_B)))),
% 1.60/1.81      inference('sup-', [status(thm)], ['177', '200'])).
% 1.60/1.81  thf('202', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.81      inference('sup-', [status(thm)], ['53', '54'])).
% 1.60/1.81  thf('203', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf('204', plain,
% 1.60/1.81      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.60/1.81         = (k7_relat_1 @ 
% 1.60/1.81            (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.60/1.81      inference('demod', [status(thm)], ['201', '202', '203'])).
% 1.60/1.81  thf('205', plain,
% 1.60/1.81      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.60/1.81          = (k7_relat_1 @ (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B) @ sk_B))
% 1.60/1.81        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.60/1.81      inference('sup+', [status(thm)], ['176', '204'])).
% 1.60/1.81  thf('206', plain,
% 1.60/1.81      (((k2_funct_1 @ sk_C) = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B))),
% 1.60/1.81      inference('demod', [status(thm)], ['184', '185', '186'])).
% 1.60/1.81  thf('207', plain,
% 1.60/1.81      (((k2_funct_1 @ sk_C) = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B))),
% 1.60/1.81      inference('demod', [status(thm)], ['184', '185', '186'])).
% 1.60/1.81  thf('208', plain,
% 1.60/1.81      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.60/1.81          = (k2_funct_1 @ sk_C))
% 1.60/1.81        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.60/1.81      inference('demod', [status(thm)], ['205', '206', '207'])).
% 1.60/1.81  thf('209', plain,
% 1.60/1.81      ((~ (v1_relat_1 @ sk_C)
% 1.60/1.81        | ~ (v1_funct_1 @ sk_C)
% 1.60/1.81        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.60/1.81            = (k2_funct_1 @ sk_C)))),
% 1.60/1.81      inference('sup-', [status(thm)], ['175', '208'])).
% 1.60/1.81  thf('210', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.81      inference('sup-', [status(thm)], ['53', '54'])).
% 1.60/1.81  thf('211', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf('212', plain,
% 1.60/1.81      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.60/1.81         = (k2_funct_1 @ sk_C))),
% 1.60/1.81      inference('demod', [status(thm)], ['209', '210', '211'])).
% 1.60/1.81  thf(t80_relat_1, axiom,
% 1.60/1.81    (![A:$i]:
% 1.60/1.81     ( ( v1_relat_1 @ A ) =>
% 1.60/1.81       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 1.60/1.81  thf('213', plain,
% 1.60/1.81      (![X14 : $i]:
% 1.60/1.81         (((k5_relat_1 @ X14 @ (k6_relat_1 @ (k2_relat_1 @ X14))) = (X14))
% 1.60/1.81          | ~ (v1_relat_1 @ X14))),
% 1.60/1.81      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.60/1.81  thf('214', plain, (![X46 : $i]: ((k6_partfun1 @ X46) = (k6_relat_1 @ X46))),
% 1.60/1.81      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.60/1.81  thf('215', plain,
% 1.60/1.81      (![X14 : $i]:
% 1.60/1.81         (((k5_relat_1 @ X14 @ (k6_partfun1 @ (k2_relat_1 @ X14))) = (X14))
% 1.60/1.81          | ~ (v1_relat_1 @ X14))),
% 1.60/1.81      inference('demod', [status(thm)], ['213', '214'])).
% 1.60/1.81  thf('216', plain,
% 1.60/1.81      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.60/1.81         (~ (v1_relat_1 @ X9)
% 1.60/1.81          | ((k5_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 1.60/1.81              = (k5_relat_1 @ X10 @ (k5_relat_1 @ X9 @ X11)))
% 1.60/1.81          | ~ (v1_relat_1 @ X11)
% 1.60/1.81          | ~ (v1_relat_1 @ X10))),
% 1.60/1.81      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.60/1.81  thf('217', plain,
% 1.60/1.81      (![X0 : $i, X1 : $i]:
% 1.60/1.81         (((k5_relat_1 @ X1 @ X0)
% 1.60/1.81            = (k5_relat_1 @ X1 @ 
% 1.60/1.81               (k5_relat_1 @ X0 @ 
% 1.60/1.81                (k6_partfun1 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))))
% 1.60/1.81          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.60/1.81          | ~ (v1_relat_1 @ X1)
% 1.60/1.81          | ~ (v1_relat_1 @ 
% 1.60/1.81               (k6_partfun1 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))
% 1.60/1.81          | ~ (v1_relat_1 @ X0))),
% 1.60/1.81      inference('sup+', [status(thm)], ['215', '216'])).
% 1.60/1.81  thf('218', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.60/1.81      inference('sup-', [status(thm)], ['84', '85'])).
% 1.60/1.81  thf('219', plain,
% 1.60/1.81      (![X0 : $i, X1 : $i]:
% 1.60/1.81         (((k5_relat_1 @ X1 @ X0)
% 1.60/1.81            = (k5_relat_1 @ X1 @ 
% 1.60/1.81               (k5_relat_1 @ X0 @ 
% 1.60/1.81                (k6_partfun1 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))))
% 1.60/1.81          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.60/1.81          | ~ (v1_relat_1 @ X1)
% 1.60/1.81          | ~ (v1_relat_1 @ X0))),
% 1.60/1.81      inference('demod', [status(thm)], ['217', '218'])).
% 1.60/1.81  thf('220', plain,
% 1.60/1.81      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.81        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.81        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 1.60/1.81        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.60/1.81            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.60/1.81               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.81                (k6_partfun1 @ 
% 1.60/1.81                 (k2_relat_1 @ 
% 1.60/1.81                  (k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))))))))),
% 1.60/1.81      inference('sup-', [status(thm)], ['212', '219'])).
% 1.60/1.81  thf('221', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.60/1.81      inference('sup-', [status(thm)], ['84', '85'])).
% 1.60/1.81  thf('222', plain,
% 1.60/1.81      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.60/1.81         = (k2_funct_1 @ sk_C))),
% 1.60/1.81      inference('demod', [status(thm)], ['209', '210', '211'])).
% 1.60/1.81  thf('223', plain,
% 1.60/1.81      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.60/1.81         = (k2_funct_1 @ sk_C))),
% 1.60/1.81      inference('demod', [status(thm)], ['209', '210', '211'])).
% 1.60/1.81  thf('224', plain,
% 1.60/1.81      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.81        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.81        | ((k2_funct_1 @ sk_C)
% 1.60/1.81            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.60/1.81               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.81                (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))))),
% 1.60/1.81      inference('demod', [status(thm)], ['220', '221', '222', '223'])).
% 1.60/1.81  thf('225', plain,
% 1.60/1.81      ((((k2_funct_1 @ sk_C)
% 1.60/1.81          = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.60/1.81             (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.81              (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))
% 1.60/1.81        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.60/1.81      inference('simplify', [status(thm)], ['224'])).
% 1.60/1.81  thf('226', plain,
% 1.60/1.81      ((~ (v1_relat_1 @ sk_C)
% 1.60/1.81        | ~ (v1_funct_1 @ sk_C)
% 1.60/1.81        | ((k2_funct_1 @ sk_C)
% 1.60/1.81            = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.60/1.81               (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.81                (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))))),
% 1.60/1.81      inference('sup-', [status(thm)], ['174', '225'])).
% 1.60/1.81  thf('227', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.81      inference('sup-', [status(thm)], ['53', '54'])).
% 1.60/1.81  thf('228', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf('229', plain,
% 1.60/1.81      (((k2_funct_1 @ sk_C)
% 1.60/1.81         = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.60/1.81            (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.81             (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 1.60/1.81      inference('demod', [status(thm)], ['226', '227', '228'])).
% 1.60/1.81  thf('230', plain,
% 1.60/1.81      ((((k2_funct_1 @ sk_C)
% 1.60/1.81          = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.60/1.81             (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.81              (k6_partfun1 @ (k1_relat_1 @ sk_C)))))
% 1.60/1.81        | ~ (v1_relat_1 @ sk_C)
% 1.60/1.81        | ~ (v1_funct_1 @ sk_C)
% 1.60/1.81        | ~ (v2_funct_1 @ sk_C))),
% 1.60/1.81      inference('sup+', [status(thm)], ['173', '229'])).
% 1.60/1.81  thf('231', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.81      inference('sup-', [status(thm)], ['53', '54'])).
% 1.60/1.81  thf('232', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf('233', plain, ((v2_funct_1 @ sk_C)),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf('234', plain,
% 1.60/1.81      (((k2_funct_1 @ sk_C)
% 1.60/1.81         = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.60/1.81            (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.81             (k6_partfun1 @ (k1_relat_1 @ sk_C)))))),
% 1.60/1.81      inference('demod', [status(thm)], ['230', '231', '232', '233'])).
% 1.60/1.81  thf('235', plain,
% 1.60/1.81      ((((k2_funct_1 @ sk_C)
% 1.60/1.81          = (k5_relat_1 @ (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B) @ 
% 1.60/1.81             (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 1.60/1.81        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.60/1.81        | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 1.60/1.81      inference('sup+', [status(thm)], ['172', '234'])).
% 1.60/1.81  thf('236', plain,
% 1.60/1.81      (((k2_funct_1 @ sk_C) = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B))),
% 1.60/1.81      inference('demod', [status(thm)], ['184', '185', '186'])).
% 1.60/1.81  thf('237', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.60/1.81      inference('sup-', [status(thm)], ['84', '85'])).
% 1.60/1.81  thf('238', plain,
% 1.60/1.81      ((((k2_funct_1 @ sk_C)
% 1.60/1.81          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.81             (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 1.60/1.81        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.60/1.81      inference('demod', [status(thm)], ['235', '236', '237'])).
% 1.60/1.81  thf('239', plain,
% 1.60/1.81      ((~ (v1_relat_1 @ sk_C)
% 1.60/1.81        | ~ (v1_funct_1 @ sk_C)
% 1.60/1.81        | ((k2_funct_1 @ sk_C)
% 1.60/1.81            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.81               (k6_partfun1 @ (k1_relat_1 @ sk_C)))))),
% 1.60/1.81      inference('sup-', [status(thm)], ['166', '238'])).
% 1.60/1.81  thf('240', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.81      inference('sup-', [status(thm)], ['53', '54'])).
% 1.60/1.81  thf('241', plain, ((v1_funct_1 @ sk_C)),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf('242', plain,
% 1.60/1.81      (((k2_funct_1 @ sk_C)
% 1.60/1.81         = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 1.60/1.81            (k6_partfun1 @ (k1_relat_1 @ sk_C))))),
% 1.60/1.81      inference('demod', [status(thm)], ['239', '240', '241'])).
% 1.60/1.81  thf('243', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 1.60/1.81      inference('demod', [status(thm)], ['159', '160', '161', '162'])).
% 1.60/1.81  thf('244', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.60/1.81      inference('sup+', [status(thm)], ['40', '41'])).
% 1.60/1.81  thf('245', plain,
% 1.60/1.81      (![X14 : $i]:
% 1.60/1.81         (((k5_relat_1 @ X14 @ (k6_partfun1 @ (k2_relat_1 @ X14))) = (X14))
% 1.60/1.81          | ~ (v1_relat_1 @ X14))),
% 1.60/1.81      inference('demod', [status(thm)], ['213', '214'])).
% 1.60/1.81  thf('246', plain,
% 1.60/1.81      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))
% 1.60/1.81        | ~ (v1_relat_1 @ sk_C))),
% 1.60/1.81      inference('sup+', [status(thm)], ['244', '245'])).
% 1.60/1.81  thf('247', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.81      inference('sup-', [status(thm)], ['53', '54'])).
% 1.60/1.81  thf('248', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.60/1.81      inference('demod', [status(thm)], ['246', '247'])).
% 1.60/1.81  thf('249', plain,
% 1.60/1.81      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.60/1.81         (~ (v1_relat_1 @ X9)
% 1.60/1.81          | ((k5_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 1.60/1.81              = (k5_relat_1 @ X10 @ (k5_relat_1 @ X9 @ X11)))
% 1.60/1.81          | ~ (v1_relat_1 @ X11)
% 1.60/1.81          | ~ (v1_relat_1 @ X10))),
% 1.60/1.81      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.60/1.81  thf('250', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         (((k5_relat_1 @ sk_C @ X0)
% 1.60/1.81            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)))
% 1.60/1.81          | ~ (v1_relat_1 @ sk_C)
% 1.60/1.81          | ~ (v1_relat_1 @ X0)
% 1.60/1.81          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B)))),
% 1.60/1.81      inference('sup+', [status(thm)], ['248', '249'])).
% 1.60/1.81  thf('251', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.81      inference('sup-', [status(thm)], ['53', '54'])).
% 1.60/1.81  thf('252', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.60/1.81      inference('sup-', [status(thm)], ['84', '85'])).
% 1.60/1.81  thf('253', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         (((k5_relat_1 @ sk_C @ X0)
% 1.60/1.81            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)))
% 1.60/1.81          | ~ (v1_relat_1 @ X0))),
% 1.60/1.81      inference('demod', [status(thm)], ['250', '251', '252'])).
% 1.60/1.81  thf('254', plain,
% 1.60/1.81      (![X7 : $i, X8 : $i]:
% 1.60/1.81         (~ (v1_relat_1 @ X7)
% 1.60/1.81          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X8 @ X7)) @ 
% 1.60/1.81             (k1_relat_1 @ X8))
% 1.60/1.81          | ~ (v1_relat_1 @ X8))),
% 1.60/1.81      inference('cnf', [status(esa)], [t44_relat_1])).
% 1.60/1.81  thf('255', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ X0)) @ 
% 1.60/1.81           (k1_relat_1 @ sk_C))
% 1.60/1.81          | ~ (v1_relat_1 @ X0)
% 1.60/1.81          | ~ (v1_relat_1 @ sk_C)
% 1.60/1.81          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)))),
% 1.60/1.81      inference('sup+', [status(thm)], ['253', '254'])).
% 1.60/1.81  thf('256', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.81      inference('sup-', [status(thm)], ['53', '54'])).
% 1.60/1.81  thf('257', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ X0)) @ 
% 1.60/1.81           (k1_relat_1 @ sk_C))
% 1.60/1.81          | ~ (v1_relat_1 @ X0)
% 1.60/1.81          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)))),
% 1.60/1.81      inference('demod', [status(thm)], ['255', '256'])).
% 1.60/1.81  thf('258', plain,
% 1.60/1.81      ((~ (v1_relat_1 @ sk_D)
% 1.60/1.81        | ~ (v1_relat_1 @ sk_D)
% 1.60/1.81        | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 1.60/1.81           (k1_relat_1 @ sk_C)))),
% 1.60/1.81      inference('sup-', [status(thm)], ['243', '257'])).
% 1.60/1.81  thf('259', plain, ((v1_relat_1 @ sk_D)),
% 1.60/1.81      inference('sup-', [status(thm)], ['132', '133'])).
% 1.60/1.81  thf('260', plain, ((v1_relat_1 @ sk_D)),
% 1.60/1.81      inference('sup-', [status(thm)], ['132', '133'])).
% 1.60/1.81  thf('261', plain,
% 1.60/1.81      ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 1.60/1.81        (k1_relat_1 @ sk_C))),
% 1.60/1.81      inference('demod', [status(thm)], ['258', '259', '260'])).
% 1.60/1.81  thf('262', plain,
% 1.60/1.81      (![X0 : $i, X2 : $i]:
% 1.60/1.81         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.60/1.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.60/1.81  thf('263', plain,
% 1.60/1.81      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ 
% 1.60/1.81           (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 1.60/1.81        | ((k1_relat_1 @ sk_C) = (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))),
% 1.60/1.81      inference('sup-', [status(thm)], ['261', '262'])).
% 1.60/1.81  thf('264', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.60/1.81      inference('demod', [status(thm)], ['24', '27'])).
% 1.60/1.81  thf('265', plain,
% 1.60/1.81      (![X12 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X12)) = (X12))),
% 1.60/1.81      inference('demod', [status(thm)], ['137', '138'])).
% 1.60/1.81  thf('266', plain,
% 1.60/1.81      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf('267', plain,
% 1.60/1.81      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.60/1.81         ((v4_relat_1 @ X23 @ X24)
% 1.60/1.81          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.60/1.81      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.60/1.81  thf('268', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 1.60/1.81      inference('sup-', [status(thm)], ['266', '267'])).
% 1.60/1.81  thf('269', plain,
% 1.60/1.81      (![X3 : $i, X4 : $i]:
% 1.60/1.81         (~ (v4_relat_1 @ X3 @ X4)
% 1.60/1.81          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.60/1.81          | ~ (v1_relat_1 @ X3))),
% 1.60/1.81      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.60/1.81  thf('270', plain,
% 1.60/1.81      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 1.60/1.81      inference('sup-', [status(thm)], ['268', '269'])).
% 1.60/1.81  thf('271', plain, ((v1_relat_1 @ sk_C)),
% 1.60/1.81      inference('sup-', [status(thm)], ['53', '54'])).
% 1.60/1.81  thf('272', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 1.60/1.81      inference('demod', [status(thm)], ['270', '271'])).
% 1.60/1.81  thf('273', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.60/1.81      inference('demod', [status(thm)], ['24', '27'])).
% 1.60/1.81  thf('274', plain,
% 1.60/1.81      (![X12 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X12)) = (X12))),
% 1.60/1.81      inference('demod', [status(thm)], ['137', '138'])).
% 1.60/1.81  thf('275', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 1.60/1.81      inference('demod', [status(thm)],
% 1.60/1.81                ['263', '264', '265', '272', '273', '274'])).
% 1.60/1.81  thf('276', plain,
% 1.60/1.81      (((k2_funct_1 @ sk_C)
% 1.60/1.81         = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))),
% 1.60/1.81      inference('demod', [status(thm)], ['242', '275'])).
% 1.60/1.81  thf('277', plain, (((k2_funct_1 @ sk_C) = (sk_D))),
% 1.60/1.81      inference('sup+', [status(thm)], ['165', '276'])).
% 1.60/1.81  thf('278', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf('279', plain, ($false),
% 1.60/1.81      inference('simplify_reflect-', [status(thm)], ['277', '278'])).
% 1.60/1.81  
% 1.60/1.81  % SZS output end Refutation
% 1.60/1.81  
% 1.67/1.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
