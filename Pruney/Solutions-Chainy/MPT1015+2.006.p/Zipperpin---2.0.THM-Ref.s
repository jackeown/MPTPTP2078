%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I03MIqZx9A

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:47 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 392 expanded)
%              Number of leaves         :   36 ( 129 expanded)
%              Depth                    :   15
%              Number of atoms          : 1097 (8895 expanded)
%              Number of equality atoms :   46 (  99 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k5_relat_1 @ X8 @ ( k2_funct_1 @ X8 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k5_relat_1 @ X8 @ ( k2_funct_1 @ X8 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('6',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 )
        = ( k5_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
      = ( k5_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['12','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( sk_B
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','26'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('28',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) @ X4 )
        = ( k5_relat_1 @ X3 @ ( k5_relat_1 @ X2 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('30',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k5_relat_1 @ X8 @ ( k2_funct_1 @ X8 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( sk_B
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','26'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('38',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( sk_B
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','26'])).

thf('41',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['37','38'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( sk_B
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','26'])).

thf('47',plain,
    ( sk_B
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','26'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('49',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k1_relset_1 @ X35 @ X35 @ X36 )
        = X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X35 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('50',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('54',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('55',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['50','51','52','55'])).

thf('57',plain,
    ( ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35','36','39','40','41','42','45','46','47','56'])).

thf('58',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','57'])).

thf('59',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['50','51','52','55'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('61',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('62',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('64',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['43','44'])).

thf('66',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['64','65'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('67',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ( ( k5_relat_1 @ X5 @ ( k6_relat_1 @ X6 ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('68',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('69',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ( ( k5_relat_1 @ X5 @ ( k6_partfun1 @ X6 ) )
        = X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_A ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['43','44'])).

thf('72',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_A ) )
    = sk_C ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['37','38'])).

thf('74',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( sk_C
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','72','73','74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 )
      | ( X18 != X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('79',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_relset_1 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['0','76','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I03MIqZx9A
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:10:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.90/1.13  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.13  % Solved by: fo/fo7.sh
% 0.90/1.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.13  % done 635 iterations in 0.681s
% 0.90/1.13  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.13  % SZS output start Refutation
% 0.90/1.13  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.90/1.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.13  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.90/1.13  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.90/1.13  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.90/1.13  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.13  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.90/1.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.90/1.13  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.90/1.13  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.90/1.13  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.90/1.13  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.90/1.13  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.13  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.90/1.13  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.13  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.90/1.13  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.90/1.13  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.90/1.13  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.13  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.90/1.13  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.90/1.13  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.90/1.13  thf(t76_funct_2, conjecture,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.90/1.13         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.90/1.13       ( ![C:$i]:
% 0.90/1.13         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.90/1.13             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.90/1.13           ( ( ( r2_relset_1 @
% 0.90/1.13                 A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 0.90/1.13               ( v2_funct_1 @ B ) ) =>
% 0.90/1.13             ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 0.90/1.13  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.13    (~( ![A:$i,B:$i]:
% 0.90/1.13        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.90/1.13            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.90/1.13          ( ![C:$i]:
% 0.90/1.13            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.90/1.13                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.90/1.13              ( ( ( r2_relset_1 @
% 0.90/1.13                    A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 0.90/1.13                  ( v2_funct_1 @ B ) ) =>
% 0.90/1.13                ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 0.90/1.13    inference('cnf.neg', [status(esa)], [t76_funct_2])).
% 0.90/1.13  thf('0', plain,
% 0.90/1.13      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_partfun1 @ sk_A))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(t61_funct_1, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.13       ( ( v2_funct_1 @ A ) =>
% 0.90/1.13         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.90/1.13             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.90/1.13           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.90/1.13             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.90/1.13  thf('1', plain,
% 0.90/1.13      (![X8 : $i]:
% 0.90/1.13         (~ (v2_funct_1 @ X8)
% 0.90/1.13          | ((k5_relat_1 @ X8 @ (k2_funct_1 @ X8))
% 0.90/1.13              = (k6_relat_1 @ (k1_relat_1 @ X8)))
% 0.90/1.13          | ~ (v1_funct_1 @ X8)
% 0.90/1.13          | ~ (v1_relat_1 @ X8))),
% 0.90/1.13      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.90/1.13  thf(redefinition_k6_partfun1, axiom,
% 0.90/1.13    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.90/1.13  thf('2', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.90/1.13      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.90/1.13  thf('3', plain,
% 0.90/1.13      (![X8 : $i]:
% 0.90/1.13         (~ (v2_funct_1 @ X8)
% 0.90/1.13          | ((k5_relat_1 @ X8 @ (k2_funct_1 @ X8))
% 0.90/1.13              = (k6_partfun1 @ (k1_relat_1 @ X8)))
% 0.90/1.13          | ~ (v1_funct_1 @ X8)
% 0.90/1.13          | ~ (v1_relat_1 @ X8))),
% 0.90/1.13      inference('demod', [status(thm)], ['1', '2'])).
% 0.90/1.13  thf('4', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('5', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(redefinition_k1_partfun1, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.90/1.13     ( ( ( v1_funct_1 @ E ) & 
% 0.90/1.13         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.90/1.13         ( v1_funct_1 @ F ) & 
% 0.90/1.13         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.90/1.13       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.90/1.13  thf('6', plain,
% 0.90/1.13      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.90/1.13          | ~ (v1_funct_1 @ X28)
% 0.90/1.13          | ~ (v1_funct_1 @ X31)
% 0.90/1.13          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.90/1.13          | ((k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31)
% 0.90/1.13              = (k5_relat_1 @ X28 @ X31)))),
% 0.90/1.13      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.90/1.13  thf('7', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.13         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 0.90/1.13            = (k5_relat_1 @ sk_C @ X0))
% 0.90/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.90/1.13          | ~ (v1_funct_1 @ X0)
% 0.90/1.13          | ~ (v1_funct_1 @ sk_C))),
% 0.90/1.13      inference('sup-', [status(thm)], ['5', '6'])).
% 0.90/1.13  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('9', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.13         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 0.90/1.13            = (k5_relat_1 @ sk_C @ X0))
% 0.90/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.90/1.13          | ~ (v1_funct_1 @ X0))),
% 0.90/1.13      inference('demod', [status(thm)], ['7', '8'])).
% 0.90/1.13  thf('10', plain,
% 0.90/1.13      ((~ (v1_funct_1 @ sk_B)
% 0.90/1.13        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 0.90/1.13            = (k5_relat_1 @ sk_C @ sk_B)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['4', '9'])).
% 0.90/1.13  thf('11', plain, ((v1_funct_1 @ sk_B)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('12', plain,
% 0.90/1.13      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.13        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ sk_B)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('13', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('14', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(dt_k1_partfun1, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.90/1.13     ( ( ( v1_funct_1 @ E ) & 
% 0.90/1.13         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.90/1.13         ( v1_funct_1 @ F ) & 
% 0.90/1.13         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.90/1.13       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.90/1.13         ( m1_subset_1 @
% 0.90/1.13           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.90/1.13           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.90/1.13  thf('15', plain,
% 0.90/1.13      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.90/1.13          | ~ (v1_funct_1 @ X22)
% 0.90/1.13          | ~ (v1_funct_1 @ X25)
% 0.90/1.13          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.90/1.13          | (m1_subset_1 @ (k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25) @ 
% 0.90/1.13             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X27))))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.90/1.13  thf('16', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.13         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 0.90/1.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.90/1.13          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.90/1.13          | ~ (v1_funct_1 @ X1)
% 0.90/1.13          | ~ (v1_funct_1 @ sk_C))),
% 0.90/1.13      inference('sup-', [status(thm)], ['14', '15'])).
% 0.90/1.13  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('18', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.90/1.13         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 0.90/1.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.90/1.13          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.90/1.13          | ~ (v1_funct_1 @ X1))),
% 0.90/1.13      inference('demod', [status(thm)], ['16', '17'])).
% 0.90/1.13  thf('19', plain,
% 0.90/1.13      ((~ (v1_funct_1 @ sk_B)
% 0.90/1.13        | (m1_subset_1 @ 
% 0.90/1.13           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 0.90/1.13           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['13', '18'])).
% 0.90/1.13  thf('20', plain, ((v1_funct_1 @ sk_B)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('21', plain,
% 0.90/1.13      ((m1_subset_1 @ 
% 0.90/1.13        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 0.90/1.13        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('demod', [status(thm)], ['19', '20'])).
% 0.90/1.13  thf(redefinition_r2_relset_1, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.13     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.90/1.13         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.90/1.13       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.90/1.13  thf('22', plain,
% 0.90/1.13      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.90/1.13          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.90/1.13          | ((X18) = (X21))
% 0.90/1.13          | ~ (r2_relset_1 @ X19 @ X20 @ X18 @ X21))),
% 0.90/1.13      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.90/1.13  thf('23', plain,
% 0.90/1.13      (![X0 : $i]:
% 0.90/1.13         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.90/1.13             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ X0)
% 0.90/1.13          | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) = (X0))
% 0.90/1.13          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['21', '22'])).
% 0.90/1.13  thf('24', plain,
% 0.90/1.13      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.90/1.13        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) = (sk_B)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['12', '23'])).
% 0.90/1.13  thf('25', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('26', plain,
% 0.90/1.13      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) = (sk_B))),
% 0.90/1.13      inference('demod', [status(thm)], ['24', '25'])).
% 0.90/1.13  thf('27', plain, (((sk_B) = (k5_relat_1 @ sk_C @ sk_B))),
% 0.90/1.13      inference('demod', [status(thm)], ['10', '11', '26'])).
% 0.90/1.13  thf(dt_k2_funct_1, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.90/1.13       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.90/1.13         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.90/1.13  thf('28', plain,
% 0.90/1.13      (![X7 : $i]:
% 0.90/1.13         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.90/1.13          | ~ (v1_funct_1 @ X7)
% 0.90/1.13          | ~ (v1_relat_1 @ X7))),
% 0.90/1.13      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.90/1.13  thf(t55_relat_1, axiom,
% 0.90/1.13    (![A:$i]:
% 0.90/1.13     ( ( v1_relat_1 @ A ) =>
% 0.90/1.13       ( ![B:$i]:
% 0.90/1.13         ( ( v1_relat_1 @ B ) =>
% 0.90/1.13           ( ![C:$i]:
% 0.90/1.13             ( ( v1_relat_1 @ C ) =>
% 0.90/1.13               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 0.90/1.13                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.90/1.13  thf('29', plain,
% 0.90/1.13      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ X2)
% 0.90/1.13          | ((k5_relat_1 @ (k5_relat_1 @ X3 @ X2) @ X4)
% 0.90/1.13              = (k5_relat_1 @ X3 @ (k5_relat_1 @ X2 @ X4)))
% 0.90/1.13          | ~ (v1_relat_1 @ X4)
% 0.90/1.13          | ~ (v1_relat_1 @ X3))),
% 0.90/1.13      inference('cnf', [status(esa)], [t55_relat_1])).
% 0.90/1.13  thf('30', plain,
% 0.90/1.13      (![X8 : $i]:
% 0.90/1.13         (~ (v2_funct_1 @ X8)
% 0.90/1.13          | ((k5_relat_1 @ X8 @ (k2_funct_1 @ X8))
% 0.90/1.13              = (k6_partfun1 @ (k1_relat_1 @ X8)))
% 0.90/1.13          | ~ (v1_funct_1 @ X8)
% 0.90/1.13          | ~ (v1_relat_1 @ X8))),
% 0.90/1.13      inference('demod', [status(thm)], ['1', '2'])).
% 0.90/1.13  thf('31', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (((k5_relat_1 @ X1 @ 
% 0.90/1.13            (k5_relat_1 @ X0 @ (k2_funct_1 @ (k5_relat_1 @ X1 @ X0))))
% 0.90/1.13            = (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))
% 0.90/1.13          | ~ (v1_relat_1 @ X1)
% 0.90/1.13          | ~ (v1_relat_1 @ (k2_funct_1 @ (k5_relat_1 @ X1 @ X0)))
% 0.90/1.13          | ~ (v1_relat_1 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.90/1.13          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.90/1.13          | ~ (v2_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.90/1.13      inference('sup+', [status(thm)], ['29', '30'])).
% 0.90/1.13  thf('32', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.90/1.13          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.90/1.13          | ~ (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.90/1.13          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.90/1.13          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 0.90/1.13          | ~ (v1_relat_1 @ X0)
% 0.90/1.13          | ~ (v1_relat_1 @ X1)
% 0.90/1.13          | ((k5_relat_1 @ X1 @ 
% 0.90/1.13              (k5_relat_1 @ X0 @ (k2_funct_1 @ (k5_relat_1 @ X1 @ X0))))
% 0.90/1.13              = (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['28', '31'])).
% 0.90/1.13  thf('33', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (((k5_relat_1 @ X1 @ 
% 0.90/1.13            (k5_relat_1 @ X0 @ (k2_funct_1 @ (k5_relat_1 @ X1 @ X0))))
% 0.90/1.13            = (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))
% 0.90/1.13          | ~ (v1_relat_1 @ X1)
% 0.90/1.13          | ~ (v1_relat_1 @ X0)
% 0.90/1.13          | ~ (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.90/1.13          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 0.90/1.13          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.90/1.13      inference('simplify', [status(thm)], ['32'])).
% 0.90/1.13  thf('34', plain,
% 0.90/1.13      ((~ (v2_funct_1 @ sk_B)
% 0.90/1.13        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))
% 0.90/1.13        | ~ (v1_funct_1 @ (k5_relat_1 @ sk_C @ sk_B))
% 0.90/1.13        | ~ (v1_relat_1 @ sk_B)
% 0.90/1.13        | ~ (v1_relat_1 @ sk_C)
% 0.90/1.13        | ((k5_relat_1 @ sk_C @ 
% 0.90/1.13            (k5_relat_1 @ sk_B @ (k2_funct_1 @ (k5_relat_1 @ sk_C @ sk_B))))
% 0.90/1.13            = (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 0.90/1.13      inference('sup-', [status(thm)], ['27', '33'])).
% 0.90/1.13  thf('35', plain, ((v2_funct_1 @ sk_B)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('36', plain, (((sk_B) = (k5_relat_1 @ sk_C @ sk_B))),
% 0.90/1.13      inference('demod', [status(thm)], ['10', '11', '26'])).
% 0.90/1.13  thf('37', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(cc1_relset_1, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i]:
% 0.90/1.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.13       ( v1_relat_1 @ C ) ))).
% 0.90/1.13  thf('38', plain,
% 0.90/1.13      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.90/1.13         ((v1_relat_1 @ X9)
% 0.90/1.13          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.90/1.13      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.90/1.13  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.90/1.13      inference('sup-', [status(thm)], ['37', '38'])).
% 0.90/1.13  thf('40', plain, (((sk_B) = (k5_relat_1 @ sk_C @ sk_B))),
% 0.90/1.13      inference('demod', [status(thm)], ['10', '11', '26'])).
% 0.90/1.13  thf('41', plain, ((v1_funct_1 @ sk_B)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.90/1.13      inference('sup-', [status(thm)], ['37', '38'])).
% 0.90/1.13  thf('43', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('44', plain,
% 0.90/1.13      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.90/1.13         ((v1_relat_1 @ X9)
% 0.90/1.13          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.90/1.13      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.90/1.13  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.13      inference('sup-', [status(thm)], ['43', '44'])).
% 0.90/1.13  thf('46', plain, (((sk_B) = (k5_relat_1 @ sk_C @ sk_B))),
% 0.90/1.13      inference('demod', [status(thm)], ['10', '11', '26'])).
% 0.90/1.13  thf('47', plain, (((sk_B) = (k5_relat_1 @ sk_C @ sk_B))),
% 0.90/1.13      inference('demod', [status(thm)], ['10', '11', '26'])).
% 0.90/1.13  thf('48', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(t67_funct_2, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.90/1.13         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.90/1.13       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.90/1.13  thf('49', plain,
% 0.90/1.13      (![X35 : $i, X36 : $i]:
% 0.90/1.13         (((k1_relset_1 @ X35 @ X35 @ X36) = (X35))
% 0.90/1.13          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))
% 0.90/1.13          | ~ (v1_funct_2 @ X36 @ X35 @ X35)
% 0.90/1.13          | ~ (v1_funct_1 @ X36))),
% 0.90/1.13      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.90/1.13  thf('50', plain,
% 0.90/1.13      ((~ (v1_funct_1 @ sk_B)
% 0.90/1.13        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.90/1.13        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['48', '49'])).
% 0.90/1.13  thf('51', plain, ((v1_funct_1 @ sk_B)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('52', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('53', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(redefinition_k1_relset_1, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i]:
% 0.90/1.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.13       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.90/1.13  thf('54', plain,
% 0.90/1.13      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.90/1.13         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.90/1.13          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.90/1.13      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.90/1.13  thf('55', plain,
% 0.90/1.13      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.90/1.13      inference('sup-', [status(thm)], ['53', '54'])).
% 0.90/1.13  thf('56', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.90/1.13      inference('demod', [status(thm)], ['50', '51', '52', '55'])).
% 0.90/1.13  thf('57', plain,
% 0.90/1.13      (((k5_relat_1 @ sk_C @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))
% 0.90/1.13         = (k6_partfun1 @ sk_A))),
% 0.90/1.13      inference('demod', [status(thm)],
% 0.90/1.13                ['34', '35', '36', '39', '40', '41', '42', '45', '46', '47', 
% 0.90/1.13                 '56'])).
% 0.90/1.13  thf('58', plain,
% 0.90/1.13      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.90/1.13          = (k6_partfun1 @ sk_A))
% 0.90/1.13        | ~ (v1_relat_1 @ sk_B)
% 0.90/1.13        | ~ (v1_funct_1 @ sk_B)
% 0.90/1.13        | ~ (v2_funct_1 @ sk_B))),
% 0.90/1.13      inference('sup+', [status(thm)], ['3', '57'])).
% 0.90/1.13  thf('59', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.90/1.13      inference('demod', [status(thm)], ['50', '51', '52', '55'])).
% 0.90/1.13  thf('60', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf(cc2_relset_1, axiom,
% 0.90/1.13    (![A:$i,B:$i,C:$i]:
% 0.90/1.13     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.90/1.13       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.90/1.13  thf('61', plain,
% 0.90/1.13      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.90/1.13         ((v5_relat_1 @ X12 @ X14)
% 0.90/1.13          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.90/1.13      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.90/1.13  thf('62', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.90/1.13      inference('sup-', [status(thm)], ['60', '61'])).
% 0.90/1.13  thf(d19_relat_1, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( v1_relat_1 @ B ) =>
% 0.90/1.13       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.90/1.13  thf('63', plain,
% 0.90/1.13      (![X0 : $i, X1 : $i]:
% 0.90/1.13         (~ (v5_relat_1 @ X0 @ X1)
% 0.90/1.13          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.90/1.13          | ~ (v1_relat_1 @ X0))),
% 0.90/1.13      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.90/1.13  thf('64', plain,
% 0.90/1.13      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A))),
% 0.90/1.13      inference('sup-', [status(thm)], ['62', '63'])).
% 0.90/1.13  thf('65', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.13      inference('sup-', [status(thm)], ['43', '44'])).
% 0.90/1.13  thf('66', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 0.90/1.13      inference('demod', [status(thm)], ['64', '65'])).
% 0.90/1.13  thf(t79_relat_1, axiom,
% 0.90/1.13    (![A:$i,B:$i]:
% 0.90/1.13     ( ( v1_relat_1 @ B ) =>
% 0.90/1.13       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.90/1.13         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.90/1.13  thf('67', plain,
% 0.90/1.13      (![X5 : $i, X6 : $i]:
% 0.90/1.13         (~ (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.90/1.13          | ((k5_relat_1 @ X5 @ (k6_relat_1 @ X6)) = (X5))
% 0.90/1.13          | ~ (v1_relat_1 @ X5))),
% 0.90/1.13      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.90/1.13  thf('68', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.90/1.13      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.90/1.13  thf('69', plain,
% 0.90/1.13      (![X5 : $i, X6 : $i]:
% 0.90/1.13         (~ (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.90/1.13          | ((k5_relat_1 @ X5 @ (k6_partfun1 @ X6)) = (X5))
% 0.90/1.13          | ~ (v1_relat_1 @ X5))),
% 0.90/1.13      inference('demod', [status(thm)], ['67', '68'])).
% 0.90/1.13  thf('70', plain,
% 0.90/1.13      ((~ (v1_relat_1 @ sk_C)
% 0.90/1.13        | ((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_A)) = (sk_C)))),
% 0.90/1.13      inference('sup-', [status(thm)], ['66', '69'])).
% 0.90/1.13  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 0.90/1.13      inference('sup-', [status(thm)], ['43', '44'])).
% 0.90/1.13  thf('72', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_A)) = (sk_C))),
% 0.90/1.13      inference('demod', [status(thm)], ['70', '71'])).
% 0.90/1.13  thf('73', plain, ((v1_relat_1 @ sk_B)),
% 0.90/1.13      inference('sup-', [status(thm)], ['37', '38'])).
% 0.90/1.13  thf('74', plain, ((v1_funct_1 @ sk_B)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('75', plain, ((v2_funct_1 @ sk_B)),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('76', plain, (((sk_C) = (k6_partfun1 @ sk_A))),
% 0.90/1.13      inference('demod', [status(thm)], ['58', '59', '72', '73', '74', '75'])).
% 0.90/1.13  thf('77', plain,
% 0.90/1.13      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.90/1.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.13  thf('78', plain,
% 0.90/1.13      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.90/1.13         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.90/1.13          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.90/1.13          | (r2_relset_1 @ X19 @ X20 @ X18 @ X21)
% 0.90/1.13          | ((X18) != (X21)))),
% 0.90/1.13      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.90/1.13  thf('79', plain,
% 0.90/1.13      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.90/1.13         ((r2_relset_1 @ X19 @ X20 @ X21 @ X21)
% 0.90/1.13          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.90/1.13      inference('simplify', [status(thm)], ['78'])).
% 0.90/1.13  thf('80', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 0.90/1.13      inference('sup-', [status(thm)], ['77', '79'])).
% 0.90/1.13  thf('81', plain, ($false),
% 0.90/1.13      inference('demod', [status(thm)], ['0', '76', '80'])).
% 0.90/1.13  
% 0.90/1.13  % SZS output end Refutation
% 0.90/1.13  
% 0.90/1.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
