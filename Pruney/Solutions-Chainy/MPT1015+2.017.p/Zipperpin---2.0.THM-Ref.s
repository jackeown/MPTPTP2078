%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CT6khbyPdR

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:49 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  237 (1494 expanded)
%              Number of leaves         :   46 ( 475 expanded)
%              Depth                    :   19
%              Number of atoms          : 2535 (30051 expanded)
%              Number of equality atoms :  106 ( 389 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(t76_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B )
              & ( v2_funct_1 @ B ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B )
                & ( v2_funct_1 @ B ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X52: $i] :
      ( ( k6_partfun1 @ X52 )
      = ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('4',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C_1 @ sk_B_1 ) @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('7',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( ( k1_partfun1 @ X47 @ X48 @ X50 @ X51 @ X46 @ X49 )
        = ( k5_relat_1 @ X46 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C_1 @ X0 )
        = ( k5_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C_1 @ X0 )
        = ( k5_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C_1 @ sk_B_1 )
      = ( k5_relat_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C_1 @ sk_B_1 )
    = ( k5_relat_1 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['4','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('17',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C_1 @ sk_B_1 )
    = ( k5_relat_1 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('25',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('26',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( X34 = X37 )
      | ~ ( r2_relset_1 @ X35 @ X36 @ X34 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_B_1 ) @ X0 )
      | ( ( k5_relat_1 @ sk_C_1 @ sk_B_1 )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C_1 @ sk_B_1 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['14','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k5_relat_1 @ sk_C_1 @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('32',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k1_relset_1 @ X60 @ X60 @ X61 )
        = X60 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X60 ) ) )
      | ~ ( v1_funct_2 @ X61 @ X60 @ X60 )
      | ~ ( v1_funct_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('33',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('37',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('38',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['33','34','35','38'])).

thf(t49_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_relat_1 @ C )
                  & ( v1_funct_1 @ C ) )
               => ( ( ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) )
                    & ( r1_tarski @ ( k2_relat_1 @ C ) @ ( k1_relat_1 @ A ) )
                    & ( ( k1_relat_1 @ B )
                      = ( k1_relat_1 @ C ) )
                    & ( ( k5_relat_1 @ B @ A )
                      = ( k5_relat_1 @ C @ A ) ) )
                 => ( B = C ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( X15 = X14 )
      | ( ( k5_relat_1 @ X15 @ X13 )
       != ( k5_relat_1 @ X14 @ X13 ) )
      | ( ( k1_relat_1 @ X15 )
       != ( k1_relat_1 @ X14 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X14 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_relat_1 @ X1 )
       != ( k1_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ X1 @ sk_B_1 )
       != ( k5_relat_1 @ X0 @ sk_B_1 ) )
      | ( X1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('43',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('45',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('46',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['33','34','35','38'])).

thf('49',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X1 ) @ sk_A )
      | ( ( k1_relat_1 @ X1 )
       != ( k1_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ X1 @ sk_B_1 )
       != ( k5_relat_1 @ X0 @ sk_B_1 ) )
      | ( X1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','46','47','48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_B_1 )
       != sk_B_1 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( X0 = sk_C_1 )
      | ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('56',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k1_relset_1 @ X60 @ X60 @ X61 )
        = X60 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X60 ) ) )
      | ~ ( v1_funct_2 @ X61 @ X60 @ X60 )
      | ~ ( v1_funct_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('60',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('65',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference(demod,[status(thm)],['60','61','62','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('68',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('69',plain,(
    v5_relat_1 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['67','68'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('70',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('71',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['54','55'])).

thf('73',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_B_1 )
       != sk_B_1 )
      | ( X0 = sk_C_1 )
      | ( ( k1_relat_1 @ X0 )
       != sk_A )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','56','57','66','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k6_relat_1 @ X0 ) )
       != sk_A )
      | ( ( k6_relat_1 @ X0 )
        = sk_C_1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B_1 )
       != sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','74'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('76',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('77',plain,(
    ! [X52: $i] :
      ( ( k6_partfun1 @ X52 )
      = ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('78',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X45 ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( X0 != sk_A )
      | ( ( k6_relat_1 @ X0 )
        = sk_C_1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B_1 )
       != sk_B_1 ) ) ),
    inference(demod,[status(thm)],['75','82','83'])).

thf('85',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B_1 )
     != sk_B_1 )
    | ( ( k6_relat_1 @ sk_A )
      = sk_C_1 )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_A @ sk_A ) ),
    inference(simplify,[status(thm)],['84'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('87',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['86'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('88',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k5_relat_1 @ X18 @ ( k2_funct_1 @ X18 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('89',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['33','34','35','38'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('90',plain,(
    ! [X59: $i] :
      ( ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X59 ) @ ( k2_relat_1 @ X59 ) ) ) )
      | ~ ( v1_funct_1 @ X59 )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('91',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['44','45'])).

thf('93',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf(t31_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf('95',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( v2_funct_1 @ X56 )
      | ( ( k2_relset_1 @ X58 @ X57 @ X56 )
       != X57 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X56 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X57 ) ) )
      | ~ ( v1_funct_2 @ X56 @ X58 @ X57 )
      | ~ ( v1_funct_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('96',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) @ sk_B_1 )
     != ( k2_relat_1 @ sk_B_1 ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['33','34','35','38'])).

thf('99',plain,(
    ! [X59: $i] :
      ( ( v1_funct_2 @ X59 @ ( k1_relat_1 @ X59 ) @ ( k2_relat_1 @ X59 ) )
      | ~ ( v1_funct_1 @ X59 )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('100',plain,
    ( ( v1_funct_2 @ sk_B_1 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['44','45'])).

thf('102',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('105',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X27 @ X25 )
        = ( k2_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('106',plain,
    ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) @ sk_B_1 )
    = ( k2_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_B_1 )
     != ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['96','97','103','106','107'])).

thf('109',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ( v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ ( k2_relat_1 @ sk_B_1 ) @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['109','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('117',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( v2_funct_1 @ X56 )
      | ( ( k2_relset_1 @ X58 @ X57 @ X56 )
       != X57 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X56 ) )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X58 @ X57 ) ) )
      | ~ ( v1_funct_2 @ X56 @ X58 @ X57 )
      | ~ ( v1_funct_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('118',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) @ sk_B_1 )
     != ( k2_relat_1 @ sk_B_1 ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('121',plain,
    ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) @ sk_B_1 )
    = ( k2_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('122',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ( ( k2_relat_1 @ sk_B_1 )
     != ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['118','119','120','121','122'])).

thf('124',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    v1_funct_1 @ ( k1_partfun1 @ sk_A @ sk_A @ ( k2_relat_1 @ sk_B_1 ) @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['115','124'])).

thf('126',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('127',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( ( k1_partfun1 @ X47 @ X48 @ X50 @ X51 @ X46 @ X49 )
        = ( k5_relat_1 @ X46 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0 )
        = ( k5_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0 )
        = ( k5_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ ( k2_relat_1 @ sk_B_1 ) @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
      = ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['126','131'])).

thf('133',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['123'])).

thf('134',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ ( k2_relat_1 @ sk_B_1 ) @ sk_A @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) )
    = ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    v1_funct_1 @ ( k5_relat_1 @ sk_B_1 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['125','134'])).

thf('136',plain,
    ( ( v1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['88','135'])).

thf('137',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['33','34','35','38'])).

thf('138',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['44','45'])).

thf('139',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['136','137','138','139','140'])).

thf('142',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B_1 )
     != sk_B_1 )
    | ( ( k6_relat_1 @ sk_A )
      = sk_C_1 ) ),
    inference('simplify_reflect+',[status(thm)],['85','87','141'])).

thf('143',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('144',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('145',plain,(
    ! [X59: $i] :
      ( ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X59 ) @ ( k2_relat_1 @ X59 ) ) ) )
      | ~ ( v1_funct_1 @ X59 )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('146',plain,(
    ! [X59: $i] :
      ( ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X59 ) @ ( k2_relat_1 @ X59 ) ) ) )
      | ~ ( v1_funct_1 @ X59 )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('147',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( ( k1_partfun1 @ X47 @ X48 @ X50 @ X51 @ X46 @ X49 )
        = ( k5_relat_1 @ X46 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('148',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X2 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ( ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X2 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['145','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ! [X59: $i] :
      ( ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X59 ) @ ( k2_relat_1 @ X59 ) ) ) )
      | ~ ( v1_funct_1 @ X59 )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('153',plain,(
    ! [X59: $i] :
      ( ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X59 ) @ ( k2_relat_1 @ X59 ) ) ) )
      | ~ ( v1_funct_1 @ X59 )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('154',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('155',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X1 @ X0 @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X1 @ X0 @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( m1_subset_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['152','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['151','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( X34 = X37 )
      | ~ ( r2_relset_1 @ X35 @ X36 @ X34 @ X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('162',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r2_relset_1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ X1 ) ) ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = X2 )
      | ~ ( r2_relset_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k2_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['144','162'])).

thf('164',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('165',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('166',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ X1 ) ) ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 )
        = X2 )
      | ~ ( r2_relset_1 @ X0 @ ( k2_relat_1 @ X1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) @ X2 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['163','164','165'])).

thf('167',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B_1 ) @ sk_B_1 )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B_1 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['143','166'])).

thf('168',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['44','45'])).

thf('169',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['136','137','138','139','140'])).

thf('171',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf(t23_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ C )
        & ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ C ) ) ) )).

thf('172',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( r2_relset_1 @ X53 @ X54 @ ( k4_relset_1 @ X53 @ X53 @ X53 @ X54 @ ( k6_partfun1 @ X53 ) @ X55 ) @ X55 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_funct_2])).

thf('173',plain,(
    ! [X52: $i] :
      ( ( k6_partfun1 @ X52 )
      = ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('174',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( r2_relset_1 @ X53 @ X54 @ ( k4_relset_1 @ X53 @ X53 @ X53 @ X54 @ ( k6_relat_1 @ X53 ) @ X55 ) @ X55 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) ) ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,(
    r2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ ( k2_relat_1 @ sk_B_1 ) @ ( k6_relat_1 @ sk_A ) @ sk_B_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['171','174'])).

thf('176',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('177',plain,(
    ! [X45: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X45 ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('178',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k4_relset_1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 )
        = ( k5_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('179',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( k4_relset_1 @ X0 @ X0 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) @ ( k6_relat_1 @ X0 ) @ sk_B_1 )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['176','179'])).

thf('181',plain,(
    r2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B_1 ) @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['175','180'])).

thf('182',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['167','168','169','170','181'])).

thf('183',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( ( k6_relat_1 @ sk_A )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['142','182'])).

thf('184',plain,
    ( ( k6_relat_1 @ sk_A )
    = sk_C_1 ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( r2_relset_1 @ X35 @ X36 @ X34 @ X37 )
      | ( X34 != X37 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('187',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( r2_relset_1 @ X35 @ X36 @ X37 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['185','187'])).

thf('189',plain,(
    $false ),
    inference(demod,[status(thm)],['2','184','188'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CT6khbyPdR
% 0.13/0.37  % Computer   : n013.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 13:33:55 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.22/0.38  % Python version: Python 3.6.8
% 0.22/0.38  % Running in FO mode
% 1.57/1.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.57/1.78  % Solved by: fo/fo7.sh
% 1.57/1.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.57/1.78  % done 2452 iterations in 1.297s
% 1.57/1.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.57/1.78  % SZS output start Refutation
% 1.57/1.78  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.57/1.78  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.57/1.78  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.57/1.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.57/1.78  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.57/1.78  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.57/1.78  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.57/1.78  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.57/1.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.57/1.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.57/1.78  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.57/1.78  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.57/1.78  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.57/1.78  thf(sk_A_type, type, sk_A: $i).
% 1.57/1.78  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.57/1.78  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.57/1.78  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.57/1.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.57/1.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.57/1.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.57/1.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.57/1.78  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.57/1.78  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.57/1.78  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.57/1.78  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 1.57/1.78  thf(t76_funct_2, conjecture,
% 1.57/1.78    (![A:$i,B:$i]:
% 1.57/1.78     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.57/1.78         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.57/1.78       ( ![C:$i]:
% 1.57/1.78         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 1.57/1.78             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.57/1.78           ( ( ( r2_relset_1 @
% 1.57/1.78                 A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 1.57/1.78               ( v2_funct_1 @ B ) ) =>
% 1.57/1.78             ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 1.57/1.78  thf(zf_stmt_0, negated_conjecture,
% 1.57/1.78    (~( ![A:$i,B:$i]:
% 1.57/1.78        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.57/1.78            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.57/1.78          ( ![C:$i]:
% 1.57/1.78            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 1.57/1.78                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.57/1.78              ( ( ( r2_relset_1 @
% 1.57/1.78                    A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 1.57/1.78                  ( v2_funct_1 @ B ) ) =>
% 1.57/1.78                ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 1.57/1.78    inference('cnf.neg', [status(esa)], [t76_funct_2])).
% 1.57/1.78  thf('0', plain,
% 1.57/1.78      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ (k6_partfun1 @ sk_A))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf(redefinition_k6_partfun1, axiom,
% 1.57/1.78    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.57/1.78  thf('1', plain, (![X52 : $i]: ((k6_partfun1 @ X52) = (k6_relat_1 @ X52))),
% 1.57/1.78      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.57/1.78  thf('2', plain,
% 1.57/1.78      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ (k6_relat_1 @ sk_A))),
% 1.57/1.78      inference('demod', [status(thm)], ['0', '1'])).
% 1.57/1.78  thf(t71_relat_1, axiom,
% 1.57/1.78    (![A:$i]:
% 1.57/1.78     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.57/1.78       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.57/1.78  thf('3', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 1.57/1.78      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.57/1.78  thf('4', plain,
% 1.57/1.78      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.57/1.78        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C_1 @ sk_B_1) @ sk_B_1)),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('5', plain,
% 1.57/1.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('6', plain,
% 1.57/1.78      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf(redefinition_k1_partfun1, axiom,
% 1.57/1.78    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.57/1.78     ( ( ( v1_funct_1 @ E ) & 
% 1.57/1.78         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.57/1.78         ( v1_funct_1 @ F ) & 
% 1.57/1.78         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.57/1.78       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.57/1.78  thf('7', plain,
% 1.57/1.78      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 1.57/1.78         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 1.57/1.78          | ~ (v1_funct_1 @ X46)
% 1.57/1.78          | ~ (v1_funct_1 @ X49)
% 1.57/1.78          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 1.57/1.78          | ((k1_partfun1 @ X47 @ X48 @ X50 @ X51 @ X46 @ X49)
% 1.57/1.78              = (k5_relat_1 @ X46 @ X49)))),
% 1.57/1.78      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.57/1.78  thf('8', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C_1 @ X0)
% 1.57/1.78            = (k5_relat_1 @ sk_C_1 @ X0))
% 1.57/1.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.57/1.78          | ~ (v1_funct_1 @ X0)
% 1.57/1.78          | ~ (v1_funct_1 @ sk_C_1))),
% 1.57/1.78      inference('sup-', [status(thm)], ['6', '7'])).
% 1.57/1.78  thf('9', plain, ((v1_funct_1 @ sk_C_1)),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('10', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C_1 @ X0)
% 1.57/1.78            = (k5_relat_1 @ sk_C_1 @ X0))
% 1.57/1.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.57/1.78          | ~ (v1_funct_1 @ X0))),
% 1.57/1.78      inference('demod', [status(thm)], ['8', '9'])).
% 1.57/1.78  thf('11', plain,
% 1.57/1.78      ((~ (v1_funct_1 @ sk_B_1)
% 1.57/1.78        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C_1 @ sk_B_1)
% 1.57/1.78            = (k5_relat_1 @ sk_C_1 @ sk_B_1)))),
% 1.57/1.78      inference('sup-', [status(thm)], ['5', '10'])).
% 1.57/1.78  thf('12', plain, ((v1_funct_1 @ sk_B_1)),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('13', plain,
% 1.57/1.78      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C_1 @ sk_B_1)
% 1.57/1.78         = (k5_relat_1 @ sk_C_1 @ sk_B_1))),
% 1.57/1.78      inference('demod', [status(thm)], ['11', '12'])).
% 1.57/1.78  thf('14', plain,
% 1.57/1.78      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C_1 @ sk_B_1) @ sk_B_1)),
% 1.57/1.78      inference('demod', [status(thm)], ['4', '13'])).
% 1.57/1.78  thf('15', plain,
% 1.57/1.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('16', plain,
% 1.57/1.78      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf(dt_k1_partfun1, axiom,
% 1.57/1.78    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.57/1.78     ( ( ( v1_funct_1 @ E ) & 
% 1.57/1.78         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.57/1.78         ( v1_funct_1 @ F ) & 
% 1.57/1.78         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.57/1.78       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.57/1.78         ( m1_subset_1 @
% 1.57/1.78           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.57/1.78           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.57/1.78  thf('17', plain,
% 1.57/1.78      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.57/1.78         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 1.57/1.78          | ~ (v1_funct_1 @ X38)
% 1.57/1.78          | ~ (v1_funct_1 @ X41)
% 1.57/1.78          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 1.57/1.78          | (m1_subset_1 @ (k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41) @ 
% 1.57/1.78             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X43))))),
% 1.57/1.78      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.57/1.78  thf('18', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 1.57/1.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.57/1.78          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.57/1.78          | ~ (v1_funct_1 @ X1)
% 1.57/1.78          | ~ (v1_funct_1 @ sk_C_1))),
% 1.57/1.78      inference('sup-', [status(thm)], ['16', '17'])).
% 1.57/1.78  thf('19', plain, ((v1_funct_1 @ sk_C_1)),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('20', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 1.57/1.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.57/1.78          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.57/1.78          | ~ (v1_funct_1 @ X1))),
% 1.57/1.78      inference('demod', [status(thm)], ['18', '19'])).
% 1.57/1.78  thf('21', plain,
% 1.57/1.78      ((~ (v1_funct_1 @ sk_B_1)
% 1.57/1.78        | (m1_subset_1 @ 
% 1.57/1.78           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C_1 @ sk_B_1) @ 
% 1.57/1.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.57/1.78      inference('sup-', [status(thm)], ['15', '20'])).
% 1.57/1.78  thf('22', plain, ((v1_funct_1 @ sk_B_1)),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('23', plain,
% 1.57/1.78      ((m1_subset_1 @ 
% 1.57/1.78        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C_1 @ sk_B_1) @ 
% 1.57/1.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.57/1.78      inference('demod', [status(thm)], ['21', '22'])).
% 1.57/1.78  thf('24', plain,
% 1.57/1.78      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C_1 @ sk_B_1)
% 1.57/1.78         = (k5_relat_1 @ sk_C_1 @ sk_B_1))),
% 1.57/1.78      inference('demod', [status(thm)], ['11', '12'])).
% 1.57/1.78  thf('25', plain,
% 1.57/1.78      ((m1_subset_1 @ (k5_relat_1 @ sk_C_1 @ sk_B_1) @ 
% 1.57/1.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.57/1.78      inference('demod', [status(thm)], ['23', '24'])).
% 1.57/1.78  thf(redefinition_r2_relset_1, axiom,
% 1.57/1.78    (![A:$i,B:$i,C:$i,D:$i]:
% 1.57/1.78     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.57/1.78         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.57/1.78       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.57/1.78  thf('26', plain,
% 1.57/1.78      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.57/1.78         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 1.57/1.78          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 1.57/1.78          | ((X34) = (X37))
% 1.57/1.78          | ~ (r2_relset_1 @ X35 @ X36 @ X34 @ X37))),
% 1.57/1.78      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.57/1.78  thf('27', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C_1 @ sk_B_1) @ X0)
% 1.57/1.78          | ((k5_relat_1 @ sk_C_1 @ sk_B_1) = (X0))
% 1.57/1.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.57/1.78      inference('sup-', [status(thm)], ['25', '26'])).
% 1.57/1.78  thf('28', plain,
% 1.57/1.78      ((~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.57/1.78        | ((k5_relat_1 @ sk_C_1 @ sk_B_1) = (sk_B_1)))),
% 1.57/1.78      inference('sup-', [status(thm)], ['14', '27'])).
% 1.57/1.78  thf('29', plain,
% 1.57/1.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('30', plain, (((k5_relat_1 @ sk_C_1 @ sk_B_1) = (sk_B_1))),
% 1.57/1.78      inference('demod', [status(thm)], ['28', '29'])).
% 1.57/1.78  thf('31', plain,
% 1.57/1.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf(t67_funct_2, axiom,
% 1.57/1.78    (![A:$i,B:$i]:
% 1.57/1.78     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.57/1.78         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.57/1.78       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 1.57/1.78  thf('32', plain,
% 1.57/1.78      (![X60 : $i, X61 : $i]:
% 1.57/1.78         (((k1_relset_1 @ X60 @ X60 @ X61) = (X60))
% 1.57/1.78          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X60)))
% 1.57/1.78          | ~ (v1_funct_2 @ X61 @ X60 @ X60)
% 1.57/1.78          | ~ (v1_funct_1 @ X61))),
% 1.57/1.78      inference('cnf', [status(esa)], [t67_funct_2])).
% 1.57/1.78  thf('33', plain,
% 1.57/1.78      ((~ (v1_funct_1 @ sk_B_1)
% 1.57/1.78        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 1.57/1.78        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (sk_A)))),
% 1.57/1.78      inference('sup-', [status(thm)], ['31', '32'])).
% 1.57/1.78  thf('34', plain, ((v1_funct_1 @ sk_B_1)),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('35', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('36', plain,
% 1.57/1.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf(redefinition_k1_relset_1, axiom,
% 1.57/1.78    (![A:$i,B:$i,C:$i]:
% 1.57/1.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.57/1.78       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.57/1.78  thf('37', plain,
% 1.57/1.78      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.57/1.78         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 1.57/1.78          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.57/1.78      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.57/1.78  thf('38', plain,
% 1.57/1.78      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 1.57/1.78      inference('sup-', [status(thm)], ['36', '37'])).
% 1.57/1.78  thf('39', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 1.57/1.78      inference('demod', [status(thm)], ['33', '34', '35', '38'])).
% 1.57/1.78  thf(t49_funct_1, axiom,
% 1.57/1.78    (![A:$i]:
% 1.57/1.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.57/1.78       ( ( v2_funct_1 @ A ) <=>
% 1.57/1.78         ( ![B:$i]:
% 1.57/1.78           ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.57/1.78             ( ![C:$i]:
% 1.57/1.78               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.57/1.78                 ( ( ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) & 
% 1.57/1.78                     ( r1_tarski @ ( k2_relat_1 @ C ) @ ( k1_relat_1 @ A ) ) & 
% 1.57/1.78                     ( ( k1_relat_1 @ B ) = ( k1_relat_1 @ C ) ) & 
% 1.57/1.78                     ( ( k5_relat_1 @ B @ A ) = ( k5_relat_1 @ C @ A ) ) ) =>
% 1.57/1.78                   ( ( B ) = ( C ) ) ) ) ) ) ) ) ))).
% 1.57/1.78  thf('40', plain,
% 1.57/1.78      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.57/1.78         (~ (v2_funct_1 @ X13)
% 1.57/1.78          | ~ (v1_relat_1 @ X14)
% 1.57/1.78          | ~ (v1_funct_1 @ X14)
% 1.57/1.78          | ((X15) = (X14))
% 1.57/1.78          | ((k5_relat_1 @ X15 @ X13) != (k5_relat_1 @ X14 @ X13))
% 1.57/1.78          | ((k1_relat_1 @ X15) != (k1_relat_1 @ X14))
% 1.57/1.78          | ~ (r1_tarski @ (k2_relat_1 @ X14) @ (k1_relat_1 @ X13))
% 1.57/1.78          | ~ (r1_tarski @ (k2_relat_1 @ X15) @ (k1_relat_1 @ X13))
% 1.57/1.78          | ~ (v1_funct_1 @ X15)
% 1.57/1.78          | ~ (v1_relat_1 @ X15)
% 1.57/1.78          | ~ (v1_funct_1 @ X13)
% 1.57/1.78          | ~ (v1_relat_1 @ X13))),
% 1.57/1.78      inference('cnf', [status(esa)], [t49_funct_1])).
% 1.57/1.78  thf('41', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         (~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_A)
% 1.57/1.78          | ~ (v1_relat_1 @ sk_B_1)
% 1.57/1.78          | ~ (v1_funct_1 @ sk_B_1)
% 1.57/1.78          | ~ (v1_relat_1 @ X1)
% 1.57/1.78          | ~ (v1_funct_1 @ X1)
% 1.57/1.78          | ~ (r1_tarski @ (k2_relat_1 @ X1) @ (k1_relat_1 @ sk_B_1))
% 1.57/1.78          | ((k1_relat_1 @ X1) != (k1_relat_1 @ X0))
% 1.57/1.78          | ((k5_relat_1 @ X1 @ sk_B_1) != (k5_relat_1 @ X0 @ sk_B_1))
% 1.57/1.78          | ((X1) = (X0))
% 1.57/1.78          | ~ (v1_funct_1 @ X0)
% 1.57/1.78          | ~ (v1_relat_1 @ X0)
% 1.57/1.78          | ~ (v2_funct_1 @ sk_B_1))),
% 1.57/1.78      inference('sup-', [status(thm)], ['39', '40'])).
% 1.57/1.78  thf('42', plain,
% 1.57/1.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf(cc2_relat_1, axiom,
% 1.57/1.78    (![A:$i]:
% 1.57/1.78     ( ( v1_relat_1 @ A ) =>
% 1.57/1.78       ( ![B:$i]:
% 1.57/1.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.57/1.78  thf('43', plain,
% 1.57/1.78      (![X3 : $i, X4 : $i]:
% 1.57/1.78         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.57/1.78          | (v1_relat_1 @ X3)
% 1.57/1.78          | ~ (v1_relat_1 @ X4))),
% 1.57/1.78      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.57/1.78  thf('44', plain,
% 1.57/1.78      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B_1))),
% 1.57/1.78      inference('sup-', [status(thm)], ['42', '43'])).
% 1.57/1.78  thf(fc6_relat_1, axiom,
% 1.57/1.78    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.57/1.78  thf('45', plain,
% 1.57/1.78      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 1.57/1.78      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.57/1.78  thf('46', plain, ((v1_relat_1 @ sk_B_1)),
% 1.57/1.78      inference('demod', [status(thm)], ['44', '45'])).
% 1.57/1.78  thf('47', plain, ((v1_funct_1 @ sk_B_1)),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('48', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 1.57/1.78      inference('demod', [status(thm)], ['33', '34', '35', '38'])).
% 1.57/1.78  thf('49', plain, ((v2_funct_1 @ sk_B_1)),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('50', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         (~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_A)
% 1.57/1.78          | ~ (v1_relat_1 @ X1)
% 1.57/1.78          | ~ (v1_funct_1 @ X1)
% 1.57/1.78          | ~ (r1_tarski @ (k2_relat_1 @ X1) @ sk_A)
% 1.57/1.78          | ((k1_relat_1 @ X1) != (k1_relat_1 @ X0))
% 1.57/1.78          | ((k5_relat_1 @ X1 @ sk_B_1) != (k5_relat_1 @ X0 @ sk_B_1))
% 1.57/1.78          | ((X1) = (X0))
% 1.57/1.78          | ~ (v1_funct_1 @ X0)
% 1.57/1.78          | ~ (v1_relat_1 @ X0))),
% 1.57/1.78      inference('demod', [status(thm)], ['41', '46', '47', '48', '49'])).
% 1.57/1.78  thf('51', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (((k5_relat_1 @ X0 @ sk_B_1) != (sk_B_1))
% 1.57/1.78          | ~ (v1_relat_1 @ sk_C_1)
% 1.57/1.78          | ~ (v1_funct_1 @ sk_C_1)
% 1.57/1.78          | ((X0) = (sk_C_1))
% 1.57/1.78          | ((k1_relat_1 @ X0) != (k1_relat_1 @ sk_C_1))
% 1.57/1.78          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_A)
% 1.57/1.78          | ~ (v1_funct_1 @ X0)
% 1.57/1.78          | ~ (v1_relat_1 @ X0)
% 1.57/1.78          | ~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_A))),
% 1.57/1.78      inference('sup-', [status(thm)], ['30', '50'])).
% 1.57/1.78  thf('52', plain,
% 1.57/1.78      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('53', plain,
% 1.57/1.78      (![X3 : $i, X4 : $i]:
% 1.57/1.78         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.57/1.78          | (v1_relat_1 @ X3)
% 1.57/1.78          | ~ (v1_relat_1 @ X4))),
% 1.57/1.78      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.57/1.78  thf('54', plain,
% 1.57/1.78      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C_1))),
% 1.57/1.78      inference('sup-', [status(thm)], ['52', '53'])).
% 1.57/1.78  thf('55', plain,
% 1.57/1.78      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 1.57/1.78      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.57/1.78  thf('56', plain, ((v1_relat_1 @ sk_C_1)),
% 1.57/1.78      inference('demod', [status(thm)], ['54', '55'])).
% 1.57/1.78  thf('57', plain, ((v1_funct_1 @ sk_C_1)),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('58', plain,
% 1.57/1.78      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('59', plain,
% 1.57/1.78      (![X60 : $i, X61 : $i]:
% 1.57/1.78         (((k1_relset_1 @ X60 @ X60 @ X61) = (X60))
% 1.57/1.78          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X60)))
% 1.57/1.78          | ~ (v1_funct_2 @ X61 @ X60 @ X60)
% 1.57/1.78          | ~ (v1_funct_1 @ X61))),
% 1.57/1.78      inference('cnf', [status(esa)], [t67_funct_2])).
% 1.57/1.78  thf('60', plain,
% 1.57/1.78      ((~ (v1_funct_1 @ sk_C_1)
% 1.57/1.78        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_A)
% 1.57/1.78        | ((k1_relset_1 @ sk_A @ sk_A @ sk_C_1) = (sk_A)))),
% 1.57/1.78      inference('sup-', [status(thm)], ['58', '59'])).
% 1.57/1.78  thf('61', plain, ((v1_funct_1 @ sk_C_1)),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('62', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_A)),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('63', plain,
% 1.57/1.78      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('64', plain,
% 1.57/1.78      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.57/1.78         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 1.57/1.78          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.57/1.78      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.57/1.78  thf('65', plain,
% 1.57/1.78      (((k1_relset_1 @ sk_A @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 1.57/1.78      inference('sup-', [status(thm)], ['63', '64'])).
% 1.57/1.78  thf('66', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 1.57/1.78      inference('demod', [status(thm)], ['60', '61', '62', '65'])).
% 1.57/1.78  thf('67', plain,
% 1.57/1.78      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf(cc2_relset_1, axiom,
% 1.57/1.78    (![A:$i,B:$i,C:$i]:
% 1.57/1.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.57/1.78       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.57/1.78  thf('68', plain,
% 1.57/1.78      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.57/1.78         ((v5_relat_1 @ X19 @ X21)
% 1.57/1.78          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.57/1.78      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.57/1.78  thf('69', plain, ((v5_relat_1 @ sk_C_1 @ sk_A)),
% 1.57/1.78      inference('sup-', [status(thm)], ['67', '68'])).
% 1.57/1.78  thf(d19_relat_1, axiom,
% 1.57/1.78    (![A:$i,B:$i]:
% 1.57/1.78     ( ( v1_relat_1 @ B ) =>
% 1.57/1.78       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.57/1.78  thf('70', plain,
% 1.57/1.78      (![X5 : $i, X6 : $i]:
% 1.57/1.78         (~ (v5_relat_1 @ X5 @ X6)
% 1.57/1.78          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 1.57/1.78          | ~ (v1_relat_1 @ X5))),
% 1.57/1.78      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.57/1.78  thf('71', plain,
% 1.57/1.78      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_A))),
% 1.57/1.78      inference('sup-', [status(thm)], ['69', '70'])).
% 1.57/1.78  thf('72', plain, ((v1_relat_1 @ sk_C_1)),
% 1.57/1.78      inference('demod', [status(thm)], ['54', '55'])).
% 1.57/1.78  thf('73', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_A)),
% 1.57/1.78      inference('demod', [status(thm)], ['71', '72'])).
% 1.57/1.78  thf('74', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (((k5_relat_1 @ X0 @ sk_B_1) != (sk_B_1))
% 1.57/1.78          | ((X0) = (sk_C_1))
% 1.57/1.78          | ((k1_relat_1 @ X0) != (sk_A))
% 1.57/1.78          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_A)
% 1.57/1.78          | ~ (v1_funct_1 @ X0)
% 1.57/1.78          | ~ (v1_relat_1 @ X0))),
% 1.57/1.78      inference('demod', [status(thm)], ['51', '56', '57', '66', '73'])).
% 1.57/1.78  thf('75', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (~ (r1_tarski @ X0 @ sk_A)
% 1.57/1.78          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.57/1.78          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 1.57/1.78          | ((k1_relat_1 @ (k6_relat_1 @ X0)) != (sk_A))
% 1.57/1.78          | ((k6_relat_1 @ X0) = (sk_C_1))
% 1.57/1.78          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B_1) != (sk_B_1)))),
% 1.57/1.78      inference('sup-', [status(thm)], ['3', '74'])).
% 1.57/1.78  thf(dt_k6_partfun1, axiom,
% 1.57/1.78    (![A:$i]:
% 1.57/1.78     ( ( m1_subset_1 @
% 1.57/1.78         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.57/1.78       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.57/1.78  thf('76', plain,
% 1.57/1.78      (![X45 : $i]:
% 1.57/1.78         (m1_subset_1 @ (k6_partfun1 @ X45) @ 
% 1.57/1.78          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X45)))),
% 1.57/1.78      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.57/1.78  thf('77', plain, (![X52 : $i]: ((k6_partfun1 @ X52) = (k6_relat_1 @ X52))),
% 1.57/1.78      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.57/1.78  thf('78', plain,
% 1.57/1.78      (![X45 : $i]:
% 1.57/1.78         (m1_subset_1 @ (k6_relat_1 @ X45) @ 
% 1.57/1.78          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X45)))),
% 1.57/1.78      inference('demod', [status(thm)], ['76', '77'])).
% 1.57/1.78  thf('79', plain,
% 1.57/1.78      (![X3 : $i, X4 : $i]:
% 1.57/1.78         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.57/1.78          | (v1_relat_1 @ X3)
% 1.57/1.78          | ~ (v1_relat_1 @ X4))),
% 1.57/1.78      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.57/1.78  thf('80', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X0))
% 1.57/1.78          | (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 1.57/1.78      inference('sup-', [status(thm)], ['78', '79'])).
% 1.57/1.78  thf('81', plain,
% 1.57/1.78      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 1.57/1.78      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.57/1.78  thf('82', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 1.57/1.78      inference('demod', [status(thm)], ['80', '81'])).
% 1.57/1.78  thf('83', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 1.57/1.78      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.57/1.78  thf('84', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         (~ (r1_tarski @ X0 @ sk_A)
% 1.57/1.78          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 1.57/1.78          | ((X0) != (sk_A))
% 1.57/1.78          | ((k6_relat_1 @ X0) = (sk_C_1))
% 1.57/1.78          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B_1) != (sk_B_1)))),
% 1.57/1.78      inference('demod', [status(thm)], ['75', '82', '83'])).
% 1.57/1.78  thf('85', plain,
% 1.57/1.78      ((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B_1) != (sk_B_1))
% 1.57/1.78        | ((k6_relat_1 @ sk_A) = (sk_C_1))
% 1.57/1.78        | ~ (v1_funct_1 @ (k6_relat_1 @ sk_A))
% 1.57/1.78        | ~ (r1_tarski @ sk_A @ sk_A))),
% 1.57/1.78      inference('simplify', [status(thm)], ['84'])).
% 1.57/1.78  thf(d10_xboole_0, axiom,
% 1.57/1.78    (![A:$i,B:$i]:
% 1.57/1.78     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.57/1.78  thf('86', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.57/1.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.57/1.78  thf('87', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.57/1.78      inference('simplify', [status(thm)], ['86'])).
% 1.57/1.78  thf(t61_funct_1, axiom,
% 1.57/1.78    (![A:$i]:
% 1.57/1.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.57/1.78       ( ( v2_funct_1 @ A ) =>
% 1.57/1.78         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.57/1.78             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.57/1.78           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.57/1.78             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.57/1.78  thf('88', plain,
% 1.57/1.78      (![X18 : $i]:
% 1.57/1.78         (~ (v2_funct_1 @ X18)
% 1.57/1.78          | ((k5_relat_1 @ X18 @ (k2_funct_1 @ X18))
% 1.57/1.78              = (k6_relat_1 @ (k1_relat_1 @ X18)))
% 1.57/1.78          | ~ (v1_funct_1 @ X18)
% 1.57/1.78          | ~ (v1_relat_1 @ X18))),
% 1.57/1.78      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.57/1.78  thf('89', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 1.57/1.78      inference('demod', [status(thm)], ['33', '34', '35', '38'])).
% 1.57/1.78  thf(t3_funct_2, axiom,
% 1.57/1.78    (![A:$i]:
% 1.57/1.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.57/1.78       ( ( v1_funct_1 @ A ) & 
% 1.57/1.78         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.57/1.78         ( m1_subset_1 @
% 1.57/1.78           A @ 
% 1.57/1.78           ( k1_zfmisc_1 @
% 1.57/1.78             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.57/1.78  thf('90', plain,
% 1.57/1.78      (![X59 : $i]:
% 1.57/1.78         ((m1_subset_1 @ X59 @ 
% 1.57/1.78           (k1_zfmisc_1 @ 
% 1.57/1.78            (k2_zfmisc_1 @ (k1_relat_1 @ X59) @ (k2_relat_1 @ X59))))
% 1.57/1.78          | ~ (v1_funct_1 @ X59)
% 1.57/1.78          | ~ (v1_relat_1 @ X59))),
% 1.57/1.78      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.57/1.78  thf('91', plain,
% 1.57/1.78      (((m1_subset_1 @ sk_B_1 @ 
% 1.57/1.78         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B_1))))
% 1.57/1.78        | ~ (v1_relat_1 @ sk_B_1)
% 1.57/1.78        | ~ (v1_funct_1 @ sk_B_1))),
% 1.57/1.78      inference('sup+', [status(thm)], ['89', '90'])).
% 1.57/1.78  thf('92', plain, ((v1_relat_1 @ sk_B_1)),
% 1.57/1.78      inference('demod', [status(thm)], ['44', '45'])).
% 1.57/1.78  thf('93', plain, ((v1_funct_1 @ sk_B_1)),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('94', plain,
% 1.57/1.78      ((m1_subset_1 @ sk_B_1 @ 
% 1.57/1.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B_1))))),
% 1.57/1.78      inference('demod', [status(thm)], ['91', '92', '93'])).
% 1.57/1.78  thf(t31_funct_2, axiom,
% 1.57/1.78    (![A:$i,B:$i,C:$i]:
% 1.57/1.78     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.57/1.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.57/1.78       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.57/1.78         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.57/1.78           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.57/1.78           ( m1_subset_1 @
% 1.57/1.78             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.57/1.78  thf('95', plain,
% 1.57/1.78      (![X56 : $i, X57 : $i, X58 : $i]:
% 1.57/1.78         (~ (v2_funct_1 @ X56)
% 1.57/1.78          | ((k2_relset_1 @ X58 @ X57 @ X56) != (X57))
% 1.57/1.78          | (m1_subset_1 @ (k2_funct_1 @ X56) @ 
% 1.57/1.78             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58)))
% 1.57/1.78          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X57)))
% 1.57/1.78          | ~ (v1_funct_2 @ X56 @ X58 @ X57)
% 1.57/1.78          | ~ (v1_funct_1 @ X56))),
% 1.57/1.78      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.57/1.78  thf('96', plain,
% 1.57/1.78      ((~ (v1_funct_1 @ sk_B_1)
% 1.57/1.78        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ (k2_relat_1 @ sk_B_1))
% 1.57/1.78        | (m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 1.57/1.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B_1) @ sk_A)))
% 1.57/1.78        | ((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B_1) @ sk_B_1)
% 1.57/1.78            != (k2_relat_1 @ sk_B_1))
% 1.57/1.78        | ~ (v2_funct_1 @ sk_B_1))),
% 1.57/1.78      inference('sup-', [status(thm)], ['94', '95'])).
% 1.57/1.78  thf('97', plain, ((v1_funct_1 @ sk_B_1)),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('98', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 1.57/1.78      inference('demod', [status(thm)], ['33', '34', '35', '38'])).
% 1.57/1.78  thf('99', plain,
% 1.57/1.78      (![X59 : $i]:
% 1.57/1.78         ((v1_funct_2 @ X59 @ (k1_relat_1 @ X59) @ (k2_relat_1 @ X59))
% 1.57/1.78          | ~ (v1_funct_1 @ X59)
% 1.57/1.78          | ~ (v1_relat_1 @ X59))),
% 1.57/1.78      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.57/1.78  thf('100', plain,
% 1.57/1.78      (((v1_funct_2 @ sk_B_1 @ sk_A @ (k2_relat_1 @ sk_B_1))
% 1.57/1.78        | ~ (v1_relat_1 @ sk_B_1)
% 1.57/1.78        | ~ (v1_funct_1 @ sk_B_1))),
% 1.57/1.78      inference('sup+', [status(thm)], ['98', '99'])).
% 1.57/1.78  thf('101', plain, ((v1_relat_1 @ sk_B_1)),
% 1.57/1.78      inference('demod', [status(thm)], ['44', '45'])).
% 1.57/1.78  thf('102', plain, ((v1_funct_1 @ sk_B_1)),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('103', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ (k2_relat_1 @ sk_B_1))),
% 1.57/1.78      inference('demod', [status(thm)], ['100', '101', '102'])).
% 1.57/1.78  thf('104', plain,
% 1.57/1.78      ((m1_subset_1 @ sk_B_1 @ 
% 1.57/1.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B_1))))),
% 1.57/1.78      inference('demod', [status(thm)], ['91', '92', '93'])).
% 1.57/1.78  thf(redefinition_k2_relset_1, axiom,
% 1.57/1.78    (![A:$i,B:$i,C:$i]:
% 1.57/1.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.57/1.78       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.57/1.78  thf('105', plain,
% 1.57/1.78      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.57/1.78         (((k2_relset_1 @ X26 @ X27 @ X25) = (k2_relat_1 @ X25))
% 1.57/1.78          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.57/1.78      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.57/1.78  thf('106', plain,
% 1.57/1.78      (((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B_1) @ sk_B_1)
% 1.57/1.78         = (k2_relat_1 @ sk_B_1))),
% 1.57/1.78      inference('sup-', [status(thm)], ['104', '105'])).
% 1.57/1.78  thf('107', plain, ((v2_funct_1 @ sk_B_1)),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('108', plain,
% 1.57/1.78      (((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 1.57/1.78         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B_1) @ sk_A)))
% 1.57/1.78        | ((k2_relat_1 @ sk_B_1) != (k2_relat_1 @ sk_B_1)))),
% 1.57/1.78      inference('demod', [status(thm)], ['96', '97', '103', '106', '107'])).
% 1.57/1.78  thf('109', plain,
% 1.57/1.78      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 1.57/1.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B_1) @ sk_A)))),
% 1.57/1.78      inference('simplify', [status(thm)], ['108'])).
% 1.57/1.78  thf('110', plain,
% 1.57/1.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('111', plain,
% 1.57/1.78      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.57/1.78         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 1.57/1.78          | ~ (v1_funct_1 @ X38)
% 1.57/1.78          | ~ (v1_funct_1 @ X41)
% 1.57/1.78          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 1.57/1.78          | (v1_funct_1 @ (k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41)))),
% 1.57/1.78      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.57/1.78  thf('112', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0))
% 1.57/1.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.57/1.78          | ~ (v1_funct_1 @ X0)
% 1.57/1.78          | ~ (v1_funct_1 @ sk_B_1))),
% 1.57/1.78      inference('sup-', [status(thm)], ['110', '111'])).
% 1.57/1.78  thf('113', plain, ((v1_funct_1 @ sk_B_1)),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('114', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         ((v1_funct_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0))
% 1.57/1.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.57/1.78          | ~ (v1_funct_1 @ X0))),
% 1.57/1.78      inference('demod', [status(thm)], ['112', '113'])).
% 1.57/1.78  thf('115', plain,
% 1.57/1.78      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 1.57/1.78        | (v1_funct_1 @ 
% 1.57/1.78           (k1_partfun1 @ sk_A @ sk_A @ (k2_relat_1 @ sk_B_1) @ sk_A @ 
% 1.57/1.78            sk_B_1 @ (k2_funct_1 @ sk_B_1))))),
% 1.57/1.78      inference('sup-', [status(thm)], ['109', '114'])).
% 1.57/1.78  thf('116', plain,
% 1.57/1.78      ((m1_subset_1 @ sk_B_1 @ 
% 1.57/1.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B_1))))),
% 1.57/1.78      inference('demod', [status(thm)], ['91', '92', '93'])).
% 1.57/1.78  thf('117', plain,
% 1.57/1.78      (![X56 : $i, X57 : $i, X58 : $i]:
% 1.57/1.78         (~ (v2_funct_1 @ X56)
% 1.57/1.78          | ((k2_relset_1 @ X58 @ X57 @ X56) != (X57))
% 1.57/1.78          | (v1_funct_1 @ (k2_funct_1 @ X56))
% 1.57/1.78          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X58 @ X57)))
% 1.57/1.78          | ~ (v1_funct_2 @ X56 @ X58 @ X57)
% 1.57/1.78          | ~ (v1_funct_1 @ X56))),
% 1.57/1.78      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.57/1.78  thf('118', plain,
% 1.57/1.78      ((~ (v1_funct_1 @ sk_B_1)
% 1.57/1.78        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ (k2_relat_1 @ sk_B_1))
% 1.57/1.78        | (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 1.57/1.78        | ((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B_1) @ sk_B_1)
% 1.57/1.78            != (k2_relat_1 @ sk_B_1))
% 1.57/1.78        | ~ (v2_funct_1 @ sk_B_1))),
% 1.57/1.78      inference('sup-', [status(thm)], ['116', '117'])).
% 1.57/1.78  thf('119', plain, ((v1_funct_1 @ sk_B_1)),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('120', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ (k2_relat_1 @ sk_B_1))),
% 1.57/1.78      inference('demod', [status(thm)], ['100', '101', '102'])).
% 1.57/1.78  thf('121', plain,
% 1.57/1.78      (((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B_1) @ sk_B_1)
% 1.57/1.78         = (k2_relat_1 @ sk_B_1))),
% 1.57/1.78      inference('sup-', [status(thm)], ['104', '105'])).
% 1.57/1.78  thf('122', plain, ((v2_funct_1 @ sk_B_1)),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('123', plain,
% 1.57/1.78      (((v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 1.57/1.78        | ((k2_relat_1 @ sk_B_1) != (k2_relat_1 @ sk_B_1)))),
% 1.57/1.78      inference('demod', [status(thm)], ['118', '119', '120', '121', '122'])).
% 1.57/1.78  thf('124', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 1.57/1.78      inference('simplify', [status(thm)], ['123'])).
% 1.57/1.78  thf('125', plain,
% 1.57/1.78      ((v1_funct_1 @ 
% 1.57/1.78        (k1_partfun1 @ sk_A @ sk_A @ (k2_relat_1 @ sk_B_1) @ sk_A @ sk_B_1 @ 
% 1.57/1.78         (k2_funct_1 @ sk_B_1)))),
% 1.57/1.78      inference('demod', [status(thm)], ['115', '124'])).
% 1.57/1.78  thf('126', plain,
% 1.57/1.78      ((m1_subset_1 @ (k2_funct_1 @ sk_B_1) @ 
% 1.57/1.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B_1) @ sk_A)))),
% 1.57/1.78      inference('simplify', [status(thm)], ['108'])).
% 1.57/1.78  thf('127', plain,
% 1.57/1.78      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('128', plain,
% 1.57/1.78      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 1.57/1.78         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 1.57/1.78          | ~ (v1_funct_1 @ X46)
% 1.57/1.78          | ~ (v1_funct_1 @ X49)
% 1.57/1.78          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 1.57/1.78          | ((k1_partfun1 @ X47 @ X48 @ X50 @ X51 @ X46 @ X49)
% 1.57/1.78              = (k5_relat_1 @ X46 @ X49)))),
% 1.57/1.78      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.57/1.78  thf('129', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0)
% 1.57/1.78            = (k5_relat_1 @ sk_B_1 @ X0))
% 1.57/1.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.57/1.78          | ~ (v1_funct_1 @ X0)
% 1.57/1.78          | ~ (v1_funct_1 @ sk_B_1))),
% 1.57/1.78      inference('sup-', [status(thm)], ['127', '128'])).
% 1.57/1.78  thf('130', plain, ((v1_funct_1 @ sk_B_1)),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('131', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B_1 @ X0)
% 1.57/1.78            = (k5_relat_1 @ sk_B_1 @ X0))
% 1.57/1.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.57/1.78          | ~ (v1_funct_1 @ X0))),
% 1.57/1.78      inference('demod', [status(thm)], ['129', '130'])).
% 1.57/1.78  thf('132', plain,
% 1.57/1.78      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B_1))
% 1.57/1.78        | ((k1_partfun1 @ sk_A @ sk_A @ (k2_relat_1 @ sk_B_1) @ sk_A @ 
% 1.57/1.78            sk_B_1 @ (k2_funct_1 @ sk_B_1))
% 1.57/1.78            = (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1))))),
% 1.57/1.78      inference('sup-', [status(thm)], ['126', '131'])).
% 1.57/1.78  thf('133', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B_1))),
% 1.57/1.78      inference('simplify', [status(thm)], ['123'])).
% 1.57/1.78  thf('134', plain,
% 1.57/1.78      (((k1_partfun1 @ sk_A @ sk_A @ (k2_relat_1 @ sk_B_1) @ sk_A @ sk_B_1 @ 
% 1.57/1.78         (k2_funct_1 @ sk_B_1)) = (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)))),
% 1.57/1.78      inference('demod', [status(thm)], ['132', '133'])).
% 1.57/1.78  thf('135', plain,
% 1.57/1.78      ((v1_funct_1 @ (k5_relat_1 @ sk_B_1 @ (k2_funct_1 @ sk_B_1)))),
% 1.57/1.78      inference('demod', [status(thm)], ['125', '134'])).
% 1.57/1.78  thf('136', plain,
% 1.57/1.78      (((v1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B_1)))
% 1.57/1.78        | ~ (v1_relat_1 @ sk_B_1)
% 1.57/1.78        | ~ (v1_funct_1 @ sk_B_1)
% 1.57/1.78        | ~ (v2_funct_1 @ sk_B_1))),
% 1.57/1.78      inference('sup+', [status(thm)], ['88', '135'])).
% 1.57/1.78  thf('137', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 1.57/1.78      inference('demod', [status(thm)], ['33', '34', '35', '38'])).
% 1.57/1.78  thf('138', plain, ((v1_relat_1 @ sk_B_1)),
% 1.57/1.78      inference('demod', [status(thm)], ['44', '45'])).
% 1.57/1.78  thf('139', plain, ((v1_funct_1 @ sk_B_1)),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('140', plain, ((v2_funct_1 @ sk_B_1)),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('141', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 1.57/1.78      inference('demod', [status(thm)], ['136', '137', '138', '139', '140'])).
% 1.57/1.78  thf('142', plain,
% 1.57/1.78      ((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B_1) != (sk_B_1))
% 1.57/1.78        | ((k6_relat_1 @ sk_A) = (sk_C_1)))),
% 1.57/1.78      inference('simplify_reflect+', [status(thm)], ['85', '87', '141'])).
% 1.57/1.78  thf('143', plain,
% 1.57/1.78      ((m1_subset_1 @ sk_B_1 @ 
% 1.57/1.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B_1))))),
% 1.57/1.78      inference('demod', [status(thm)], ['91', '92', '93'])).
% 1.57/1.78  thf('144', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 1.57/1.78      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.57/1.78  thf('145', plain,
% 1.57/1.78      (![X59 : $i]:
% 1.57/1.78         ((m1_subset_1 @ X59 @ 
% 1.57/1.78           (k1_zfmisc_1 @ 
% 1.57/1.78            (k2_zfmisc_1 @ (k1_relat_1 @ X59) @ (k2_relat_1 @ X59))))
% 1.57/1.78          | ~ (v1_funct_1 @ X59)
% 1.57/1.78          | ~ (v1_relat_1 @ X59))),
% 1.57/1.78      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.57/1.78  thf('146', plain,
% 1.57/1.78      (![X59 : $i]:
% 1.57/1.78         ((m1_subset_1 @ X59 @ 
% 1.57/1.78           (k1_zfmisc_1 @ 
% 1.57/1.78            (k2_zfmisc_1 @ (k1_relat_1 @ X59) @ (k2_relat_1 @ X59))))
% 1.57/1.78          | ~ (v1_funct_1 @ X59)
% 1.57/1.78          | ~ (v1_relat_1 @ X59))),
% 1.57/1.78      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.57/1.78  thf('147', plain,
% 1.57/1.78      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 1.57/1.78         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 1.57/1.78          | ~ (v1_funct_1 @ X46)
% 1.57/1.78          | ~ (v1_funct_1 @ X49)
% 1.57/1.78          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 1.57/1.78          | ((k1_partfun1 @ X47 @ X48 @ X50 @ X51 @ X46 @ X49)
% 1.57/1.78              = (k5_relat_1 @ X46 @ X49)))),
% 1.57/1.78      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.57/1.78  thf('148', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.57/1.78         (~ (v1_relat_1 @ X0)
% 1.57/1.78          | ~ (v1_funct_1 @ X0)
% 1.57/1.78          | ((k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X2 @ 
% 1.57/1.78              X0 @ X1) = (k5_relat_1 @ X0 @ X1))
% 1.57/1.78          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 1.57/1.78          | ~ (v1_funct_1 @ X1)
% 1.57/1.78          | ~ (v1_funct_1 @ X0))),
% 1.57/1.78      inference('sup-', [status(thm)], ['146', '147'])).
% 1.57/1.78  thf('149', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.57/1.78         (~ (v1_funct_1 @ X1)
% 1.57/1.78          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 1.57/1.78          | ((k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X2 @ 
% 1.57/1.78              X0 @ X1) = (k5_relat_1 @ X0 @ X1))
% 1.57/1.78          | ~ (v1_funct_1 @ X0)
% 1.57/1.78          | ~ (v1_relat_1 @ X0))),
% 1.57/1.78      inference('simplify', [status(thm)], ['148'])).
% 1.57/1.78  thf('150', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         (~ (v1_relat_1 @ X0)
% 1.57/1.78          | ~ (v1_funct_1 @ X0)
% 1.57/1.78          | ~ (v1_relat_1 @ X1)
% 1.57/1.78          | ~ (v1_funct_1 @ X1)
% 1.57/1.78          | ((k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 1.57/1.78              (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0)
% 1.57/1.78              = (k5_relat_1 @ X1 @ X0))
% 1.57/1.78          | ~ (v1_funct_1 @ X0))),
% 1.57/1.78      inference('sup-', [status(thm)], ['145', '149'])).
% 1.57/1.78  thf('151', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         (((k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 1.57/1.78            (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0)
% 1.57/1.78            = (k5_relat_1 @ X1 @ X0))
% 1.57/1.78          | ~ (v1_funct_1 @ X1)
% 1.57/1.78          | ~ (v1_relat_1 @ X1)
% 1.57/1.78          | ~ (v1_funct_1 @ X0)
% 1.57/1.78          | ~ (v1_relat_1 @ X0))),
% 1.57/1.78      inference('simplify', [status(thm)], ['150'])).
% 1.57/1.78  thf('152', plain,
% 1.57/1.78      (![X59 : $i]:
% 1.57/1.78         ((m1_subset_1 @ X59 @ 
% 1.57/1.78           (k1_zfmisc_1 @ 
% 1.57/1.78            (k2_zfmisc_1 @ (k1_relat_1 @ X59) @ (k2_relat_1 @ X59))))
% 1.57/1.78          | ~ (v1_funct_1 @ X59)
% 1.57/1.78          | ~ (v1_relat_1 @ X59))),
% 1.57/1.78      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.57/1.78  thf('153', plain,
% 1.57/1.78      (![X59 : $i]:
% 1.57/1.78         ((m1_subset_1 @ X59 @ 
% 1.57/1.78           (k1_zfmisc_1 @ 
% 1.57/1.78            (k2_zfmisc_1 @ (k1_relat_1 @ X59) @ (k2_relat_1 @ X59))))
% 1.57/1.78          | ~ (v1_funct_1 @ X59)
% 1.57/1.78          | ~ (v1_relat_1 @ X59))),
% 1.57/1.78      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.57/1.78  thf('154', plain,
% 1.57/1.78      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.57/1.78         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 1.57/1.78          | ~ (v1_funct_1 @ X38)
% 1.57/1.78          | ~ (v1_funct_1 @ X41)
% 1.57/1.78          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 1.57/1.78          | (m1_subset_1 @ (k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41) @ 
% 1.57/1.78             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X43))))),
% 1.57/1.78      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.57/1.78  thf('155', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.57/1.78         (~ (v1_relat_1 @ X0)
% 1.57/1.78          | ~ (v1_funct_1 @ X0)
% 1.57/1.78          | (m1_subset_1 @ 
% 1.57/1.78             (k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X1 @ 
% 1.57/1.78              X0 @ X2) @ 
% 1.57/1.78             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 1.57/1.78          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1)))
% 1.57/1.78          | ~ (v1_funct_1 @ X2)
% 1.57/1.78          | ~ (v1_funct_1 @ X0))),
% 1.57/1.78      inference('sup-', [status(thm)], ['153', '154'])).
% 1.57/1.78  thf('156', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.57/1.78         (~ (v1_funct_1 @ X2)
% 1.57/1.78          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1)))
% 1.57/1.78          | (m1_subset_1 @ 
% 1.57/1.78             (k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X1 @ 
% 1.57/1.78              X0 @ X2) @ 
% 1.57/1.78             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 1.57/1.78          | ~ (v1_funct_1 @ X0)
% 1.57/1.78          | ~ (v1_relat_1 @ X0))),
% 1.57/1.78      inference('simplify', [status(thm)], ['155'])).
% 1.57/1.78  thf('157', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         (~ (v1_relat_1 @ X0)
% 1.57/1.78          | ~ (v1_funct_1 @ X0)
% 1.57/1.78          | ~ (v1_relat_1 @ X1)
% 1.57/1.78          | ~ (v1_funct_1 @ X1)
% 1.57/1.78          | (m1_subset_1 @ 
% 1.57/1.78             (k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 1.57/1.78              (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0) @ 
% 1.57/1.78             (k1_zfmisc_1 @ 
% 1.57/1.78              (k2_zfmisc_1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X0))))
% 1.57/1.78          | ~ (v1_funct_1 @ X0))),
% 1.57/1.78      inference('sup-', [status(thm)], ['152', '156'])).
% 1.57/1.78  thf('158', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((m1_subset_1 @ 
% 1.57/1.78           (k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 1.57/1.78            (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0) @ 
% 1.57/1.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X0))))
% 1.57/1.78          | ~ (v1_funct_1 @ X1)
% 1.57/1.78          | ~ (v1_relat_1 @ X1)
% 1.57/1.78          | ~ (v1_funct_1 @ X0)
% 1.57/1.78          | ~ (v1_relat_1 @ X0))),
% 1.57/1.78      inference('simplify', [status(thm)], ['157'])).
% 1.57/1.78  thf('159', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         ((m1_subset_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 1.57/1.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X0))))
% 1.57/1.78          | ~ (v1_relat_1 @ X0)
% 1.57/1.78          | ~ (v1_funct_1 @ X0)
% 1.57/1.78          | ~ (v1_relat_1 @ X1)
% 1.57/1.78          | ~ (v1_funct_1 @ X1)
% 1.57/1.78          | ~ (v1_relat_1 @ X0)
% 1.57/1.78          | ~ (v1_funct_1 @ X0)
% 1.57/1.78          | ~ (v1_relat_1 @ X1)
% 1.57/1.78          | ~ (v1_funct_1 @ X1))),
% 1.57/1.78      inference('sup+', [status(thm)], ['151', '158'])).
% 1.57/1.78  thf('160', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i]:
% 1.57/1.78         (~ (v1_funct_1 @ X1)
% 1.57/1.78          | ~ (v1_relat_1 @ X1)
% 1.57/1.78          | ~ (v1_funct_1 @ X0)
% 1.57/1.78          | ~ (v1_relat_1 @ X0)
% 1.57/1.78          | (m1_subset_1 @ (k5_relat_1 @ X1 @ X0) @ 
% 1.57/1.78             (k1_zfmisc_1 @ 
% 1.57/1.78              (k2_zfmisc_1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X0)))))),
% 1.57/1.78      inference('simplify', [status(thm)], ['159'])).
% 1.57/1.78  thf('161', plain,
% 1.57/1.78      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.57/1.78         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 1.57/1.78          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 1.57/1.78          | ((X34) = (X37))
% 1.57/1.78          | ~ (r2_relset_1 @ X35 @ X36 @ X34 @ X37))),
% 1.57/1.78      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.57/1.78  thf('162', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         (~ (v1_relat_1 @ X0)
% 1.57/1.78          | ~ (v1_funct_1 @ X0)
% 1.57/1.78          | ~ (v1_relat_1 @ X1)
% 1.57/1.78          | ~ (v1_funct_1 @ X1)
% 1.57/1.78          | ~ (r2_relset_1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X0) @ 
% 1.57/1.78               (k5_relat_1 @ X1 @ X0) @ X2)
% 1.57/1.78          | ((k5_relat_1 @ X1 @ X0) = (X2))
% 1.57/1.78          | ~ (m1_subset_1 @ X2 @ 
% 1.57/1.78               (k1_zfmisc_1 @ 
% 1.57/1.78                (k2_zfmisc_1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X0)))))),
% 1.57/1.78      inference('sup-', [status(thm)], ['160', '161'])).
% 1.57/1.78  thf('163', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         (~ (m1_subset_1 @ X2 @ 
% 1.57/1.78             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ X1))))
% 1.57/1.78          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ X1) = (X2))
% 1.57/1.78          | ~ (r2_relset_1 @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ 
% 1.57/1.78               (k2_relat_1 @ X1) @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X2)
% 1.57/1.78          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 1.57/1.78          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.57/1.78          | ~ (v1_funct_1 @ X1)
% 1.57/1.78          | ~ (v1_relat_1 @ X1))),
% 1.57/1.78      inference('sup-', [status(thm)], ['144', '162'])).
% 1.57/1.78  thf('164', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 1.57/1.78      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.57/1.78  thf('165', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 1.57/1.78      inference('demod', [status(thm)], ['80', '81'])).
% 1.57/1.78  thf('166', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.57/1.78         (~ (m1_subset_1 @ X2 @ 
% 1.57/1.78             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ X1))))
% 1.57/1.78          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ X1) = (X2))
% 1.57/1.78          | ~ (r2_relset_1 @ X0 @ (k2_relat_1 @ X1) @ 
% 1.57/1.78               (k5_relat_1 @ (k6_relat_1 @ X0) @ X1) @ X2)
% 1.57/1.78          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 1.57/1.78          | ~ (v1_funct_1 @ X1)
% 1.57/1.78          | ~ (v1_relat_1 @ X1))),
% 1.57/1.78      inference('demod', [status(thm)], ['163', '164', '165'])).
% 1.57/1.78  thf('167', plain,
% 1.57/1.78      ((~ (v1_relat_1 @ sk_B_1)
% 1.57/1.78        | ~ (v1_funct_1 @ sk_B_1)
% 1.57/1.78        | ~ (v1_funct_1 @ (k6_relat_1 @ sk_A))
% 1.57/1.78        | ~ (r2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B_1) @ 
% 1.57/1.78             (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B_1) @ sk_B_1)
% 1.57/1.78        | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B_1) = (sk_B_1)))),
% 1.57/1.78      inference('sup-', [status(thm)], ['143', '166'])).
% 1.57/1.78  thf('168', plain, ((v1_relat_1 @ sk_B_1)),
% 1.57/1.78      inference('demod', [status(thm)], ['44', '45'])).
% 1.57/1.78  thf('169', plain, ((v1_funct_1 @ sk_B_1)),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('170', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 1.57/1.78      inference('demod', [status(thm)], ['136', '137', '138', '139', '140'])).
% 1.57/1.78  thf('171', plain,
% 1.57/1.78      ((m1_subset_1 @ sk_B_1 @ 
% 1.57/1.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B_1))))),
% 1.57/1.78      inference('demod', [status(thm)], ['91', '92', '93'])).
% 1.57/1.78  thf(t23_funct_2, axiom,
% 1.57/1.78    (![A:$i,B:$i,C:$i]:
% 1.57/1.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.57/1.78       ( ( r2_relset_1 @
% 1.57/1.78           A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ 
% 1.57/1.78           C ) & 
% 1.57/1.78         ( r2_relset_1 @
% 1.57/1.78           A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ 
% 1.57/1.78           C ) ) ))).
% 1.57/1.78  thf('172', plain,
% 1.57/1.78      (![X53 : $i, X54 : $i, X55 : $i]:
% 1.57/1.78         ((r2_relset_1 @ X53 @ X54 @ 
% 1.57/1.78           (k4_relset_1 @ X53 @ X53 @ X53 @ X54 @ (k6_partfun1 @ X53) @ X55) @ 
% 1.57/1.78           X55)
% 1.57/1.78          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54))))),
% 1.57/1.78      inference('cnf', [status(esa)], [t23_funct_2])).
% 1.57/1.78  thf('173', plain, (![X52 : $i]: ((k6_partfun1 @ X52) = (k6_relat_1 @ X52))),
% 1.57/1.78      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.57/1.78  thf('174', plain,
% 1.57/1.78      (![X53 : $i, X54 : $i, X55 : $i]:
% 1.57/1.78         ((r2_relset_1 @ X53 @ X54 @ 
% 1.57/1.78           (k4_relset_1 @ X53 @ X53 @ X53 @ X54 @ (k6_relat_1 @ X53) @ X55) @ 
% 1.57/1.78           X55)
% 1.57/1.78          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54))))),
% 1.57/1.78      inference('demod', [status(thm)], ['172', '173'])).
% 1.57/1.78  thf('175', plain,
% 1.57/1.78      ((r2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B_1) @ 
% 1.57/1.78        (k4_relset_1 @ sk_A @ sk_A @ sk_A @ (k2_relat_1 @ sk_B_1) @ 
% 1.57/1.78         (k6_relat_1 @ sk_A) @ sk_B_1) @ 
% 1.57/1.78        sk_B_1)),
% 1.57/1.78      inference('sup-', [status(thm)], ['171', '174'])).
% 1.57/1.78  thf('176', plain,
% 1.57/1.78      ((m1_subset_1 @ sk_B_1 @ 
% 1.57/1.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B_1))))),
% 1.57/1.78      inference('demod', [status(thm)], ['91', '92', '93'])).
% 1.57/1.78  thf('177', plain,
% 1.57/1.78      (![X45 : $i]:
% 1.57/1.78         (m1_subset_1 @ (k6_relat_1 @ X45) @ 
% 1.57/1.78          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X45)))),
% 1.57/1.78      inference('demod', [status(thm)], ['76', '77'])).
% 1.57/1.78  thf(redefinition_k4_relset_1, axiom,
% 1.57/1.78    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.57/1.78     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.57/1.78         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.57/1.78       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.57/1.78  thf('178', plain,
% 1.57/1.78      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.57/1.78         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 1.57/1.78          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.57/1.78          | ((k4_relset_1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31)
% 1.57/1.78              = (k5_relat_1 @ X28 @ X31)))),
% 1.57/1.78      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 1.57/1.78  thf('179', plain,
% 1.57/1.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.57/1.78         (((k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ (k6_relat_1 @ X0) @ X1)
% 1.57/1.78            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 1.57/1.78          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2))))),
% 1.57/1.78      inference('sup-', [status(thm)], ['177', '178'])).
% 1.57/1.78  thf('180', plain,
% 1.57/1.78      (![X0 : $i]:
% 1.57/1.78         ((k4_relset_1 @ X0 @ X0 @ sk_A @ (k2_relat_1 @ sk_B_1) @ 
% 1.57/1.78           (k6_relat_1 @ X0) @ sk_B_1)
% 1.57/1.78           = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B_1))),
% 1.57/1.78      inference('sup-', [status(thm)], ['176', '179'])).
% 1.57/1.78  thf('181', plain,
% 1.57/1.78      ((r2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B_1) @ 
% 1.57/1.78        (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B_1) @ sk_B_1)),
% 1.57/1.78      inference('demod', [status(thm)], ['175', '180'])).
% 1.57/1.78  thf('182', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B_1) = (sk_B_1))),
% 1.57/1.78      inference('demod', [status(thm)], ['167', '168', '169', '170', '181'])).
% 1.57/1.78  thf('183', plain,
% 1.57/1.78      ((((sk_B_1) != (sk_B_1)) | ((k6_relat_1 @ sk_A) = (sk_C_1)))),
% 1.57/1.78      inference('demod', [status(thm)], ['142', '182'])).
% 1.57/1.78  thf('184', plain, (((k6_relat_1 @ sk_A) = (sk_C_1))),
% 1.57/1.78      inference('simplify', [status(thm)], ['183'])).
% 1.57/1.78  thf('185', plain,
% 1.57/1.78      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.57/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.57/1.78  thf('186', plain,
% 1.57/1.78      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.57/1.78         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 1.57/1.78          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 1.57/1.78          | (r2_relset_1 @ X35 @ X36 @ X34 @ X37)
% 1.57/1.78          | ((X34) != (X37)))),
% 1.57/1.78      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.57/1.78  thf('187', plain,
% 1.57/1.78      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.57/1.78         ((r2_relset_1 @ X35 @ X36 @ X37 @ X37)
% 1.57/1.78          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 1.57/1.78      inference('simplify', [status(thm)], ['186'])).
% 1.57/1.78  thf('188', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C_1 @ sk_C_1)),
% 1.57/1.78      inference('sup-', [status(thm)], ['185', '187'])).
% 1.57/1.78  thf('189', plain, ($false),
% 1.57/1.78      inference('demod', [status(thm)], ['2', '184', '188'])).
% 1.57/1.78  
% 1.57/1.78  % SZS output end Refutation
% 1.57/1.78  
% 1.57/1.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
