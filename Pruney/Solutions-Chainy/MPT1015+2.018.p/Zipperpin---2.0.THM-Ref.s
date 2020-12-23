%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LrrdvMcVZ0

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:49 EST 2020

% Result     : Theorem 1.00s
% Output     : Refutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 410 expanded)
%              Number of leaves         :   37 ( 135 expanded)
%              Depth                    :   15
%              Number of atoms          : 1121 (8979 expanded)
%              Number of equality atoms :   46 (  99 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ X12 @ ( k2_funct_1 @ X12 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ X12 @ ( k2_funct_1 @ X12 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 )
        = ( k5_relat_1 @ X29 @ X32 ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X28 ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( X19 = X22 )
      | ~ ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 ) ) ),
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
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) @ X8 )
        = ( k5_relat_1 @ X7 @ ( k5_relat_1 @ X6 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('30',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k5_relat_1 @ X12 @ ( k2_funct_1 @ X12 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( sk_B
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','26'])).

thf('43',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['39','40'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('49',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( sk_B
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','26'])).

thf('51',plain,
    ( sk_B
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','26'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('53',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k1_relset_1 @ X36 @ X36 @ X37 )
        = X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X36 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('54',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('58',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('59',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['54','55','56','59'])).

thf('61',plain,
    ( ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35','36','41','42','43','44','49','50','51','60'])).

thf('62',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['3','61'])).

thf('63',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['54','55','56','59'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('65',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('66',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['64','65'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('67',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v5_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('70',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['68','69'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('71',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ( ( k5_relat_1 @ X9 @ ( k6_relat_1 @ X10 ) )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('72',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('73',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ( ( k5_relat_1 @ X9 @ ( k6_partfun1 @ X10 ) )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_A ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['47','48'])).

thf('76',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_A ) )
    = sk_C ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['39','40'])).

thf('78',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( sk_C
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63','76','77','78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 )
      | ( X19 != X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('83',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r2_relset_1 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['81','83'])).

thf('85',plain,(
    $false ),
    inference(demod,[status(thm)],['0','80','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LrrdvMcVZ0
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:01:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.00/1.18  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.00/1.18  % Solved by: fo/fo7.sh
% 1.00/1.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.00/1.18  % done 635 iterations in 0.733s
% 1.00/1.18  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.00/1.18  % SZS output start Refutation
% 1.00/1.18  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.00/1.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.00/1.18  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.00/1.18  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.00/1.18  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.00/1.18  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.00/1.18  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.00/1.18  thf(sk_C_type, type, sk_C: $i).
% 1.00/1.18  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.00/1.18  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.00/1.18  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.00/1.18  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.00/1.18  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.00/1.18  thf(sk_A_type, type, sk_A: $i).
% 1.00/1.18  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.00/1.18  thf(sk_B_type, type, sk_B: $i).
% 1.00/1.18  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.00/1.18  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.00/1.18  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.00/1.18  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.00/1.18  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.00/1.18  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.00/1.18  thf(t76_funct_2, conjecture,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.00/1.18         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.00/1.18       ( ![C:$i]:
% 1.00/1.18         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 1.00/1.18             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.00/1.18           ( ( ( r2_relset_1 @
% 1.00/1.18                 A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 1.00/1.18               ( v2_funct_1 @ B ) ) =>
% 1.00/1.18             ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 1.00/1.18  thf(zf_stmt_0, negated_conjecture,
% 1.00/1.18    (~( ![A:$i,B:$i]:
% 1.00/1.18        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.00/1.18            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.00/1.18          ( ![C:$i]:
% 1.00/1.18            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 1.00/1.18                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.00/1.18              ( ( ( r2_relset_1 @
% 1.00/1.18                    A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 1.00/1.18                  ( v2_funct_1 @ B ) ) =>
% 1.00/1.18                ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 1.00/1.18    inference('cnf.neg', [status(esa)], [t76_funct_2])).
% 1.00/1.18  thf('0', plain,
% 1.00/1.18      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_partfun1 @ sk_A))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf(t61_funct_1, axiom,
% 1.00/1.18    (![A:$i]:
% 1.00/1.18     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.00/1.18       ( ( v2_funct_1 @ A ) =>
% 1.00/1.18         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.00/1.18             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.00/1.18           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.00/1.18             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.00/1.18  thf('1', plain,
% 1.00/1.18      (![X12 : $i]:
% 1.00/1.18         (~ (v2_funct_1 @ X12)
% 1.00/1.18          | ((k5_relat_1 @ X12 @ (k2_funct_1 @ X12))
% 1.00/1.18              = (k6_relat_1 @ (k1_relat_1 @ X12)))
% 1.00/1.18          | ~ (v1_funct_1 @ X12)
% 1.00/1.18          | ~ (v1_relat_1 @ X12))),
% 1.00/1.18      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.00/1.18  thf(redefinition_k6_partfun1, axiom,
% 1.00/1.18    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.00/1.18  thf('2', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 1.00/1.18      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.00/1.18  thf('3', plain,
% 1.00/1.18      (![X12 : $i]:
% 1.00/1.18         (~ (v2_funct_1 @ X12)
% 1.00/1.18          | ((k5_relat_1 @ X12 @ (k2_funct_1 @ X12))
% 1.00/1.18              = (k6_partfun1 @ (k1_relat_1 @ X12)))
% 1.00/1.18          | ~ (v1_funct_1 @ X12)
% 1.00/1.18          | ~ (v1_relat_1 @ X12))),
% 1.00/1.18      inference('demod', [status(thm)], ['1', '2'])).
% 1.00/1.18  thf('4', plain,
% 1.00/1.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('5', plain,
% 1.00/1.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf(redefinition_k1_partfun1, axiom,
% 1.00/1.18    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.00/1.18     ( ( ( v1_funct_1 @ E ) & 
% 1.00/1.18         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.00/1.18         ( v1_funct_1 @ F ) & 
% 1.00/1.18         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.00/1.18       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.00/1.18  thf('6', plain,
% 1.00/1.18      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.00/1.18         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 1.00/1.18          | ~ (v1_funct_1 @ X29)
% 1.00/1.18          | ~ (v1_funct_1 @ X32)
% 1.00/1.18          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.00/1.18          | ((k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)
% 1.00/1.18              = (k5_relat_1 @ X29 @ X32)))),
% 1.00/1.18      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.00/1.18  thf('7', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.18         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 1.00/1.18            = (k5_relat_1 @ sk_C @ X0))
% 1.00/1.18          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.00/1.18          | ~ (v1_funct_1 @ X0)
% 1.00/1.18          | ~ (v1_funct_1 @ sk_C))),
% 1.00/1.18      inference('sup-', [status(thm)], ['5', '6'])).
% 1.00/1.18  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('9', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.18         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 1.00/1.18            = (k5_relat_1 @ sk_C @ X0))
% 1.00/1.18          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.00/1.18          | ~ (v1_funct_1 @ X0))),
% 1.00/1.18      inference('demod', [status(thm)], ['7', '8'])).
% 1.00/1.18  thf('10', plain,
% 1.00/1.18      ((~ (v1_funct_1 @ sk_B)
% 1.00/1.18        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 1.00/1.18            = (k5_relat_1 @ sk_C @ sk_B)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['4', '9'])).
% 1.00/1.18  thf('11', plain, ((v1_funct_1 @ sk_B)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('12', plain,
% 1.00/1.18      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.00/1.18        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ sk_B)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('13', plain,
% 1.00/1.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('14', plain,
% 1.00/1.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf(dt_k1_partfun1, axiom,
% 1.00/1.18    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.00/1.18     ( ( ( v1_funct_1 @ E ) & 
% 1.00/1.18         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.00/1.18         ( v1_funct_1 @ F ) & 
% 1.00/1.18         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.00/1.18       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.00/1.18         ( m1_subset_1 @
% 1.00/1.18           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.00/1.18           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.00/1.18  thf('15', plain,
% 1.00/1.18      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.00/1.18         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 1.00/1.18          | ~ (v1_funct_1 @ X23)
% 1.00/1.18          | ~ (v1_funct_1 @ X26)
% 1.00/1.18          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.00/1.18          | (m1_subset_1 @ (k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26) @ 
% 1.00/1.18             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X28))))),
% 1.00/1.18      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.00/1.18  thf('16', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.18         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 1.00/1.18           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.00/1.18          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.00/1.18          | ~ (v1_funct_1 @ X1)
% 1.00/1.18          | ~ (v1_funct_1 @ sk_C))),
% 1.00/1.18      inference('sup-', [status(thm)], ['14', '15'])).
% 1.00/1.18  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('18', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.00/1.18         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 1.00/1.18           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.00/1.18          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.00/1.18          | ~ (v1_funct_1 @ X1))),
% 1.00/1.18      inference('demod', [status(thm)], ['16', '17'])).
% 1.00/1.18  thf('19', plain,
% 1.00/1.18      ((~ (v1_funct_1 @ sk_B)
% 1.00/1.18        | (m1_subset_1 @ 
% 1.00/1.18           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 1.00/1.18           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.00/1.18      inference('sup-', [status(thm)], ['13', '18'])).
% 1.00/1.18  thf('20', plain, ((v1_funct_1 @ sk_B)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('21', plain,
% 1.00/1.18      ((m1_subset_1 @ 
% 1.00/1.18        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 1.00/1.18        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.00/1.18      inference('demod', [status(thm)], ['19', '20'])).
% 1.00/1.18  thf(redefinition_r2_relset_1, axiom,
% 1.00/1.18    (![A:$i,B:$i,C:$i,D:$i]:
% 1.00/1.18     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.00/1.18         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.00/1.18       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.00/1.18  thf('22', plain,
% 1.00/1.18      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.00/1.18         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.00/1.18          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.00/1.18          | ((X19) = (X22))
% 1.00/1.18          | ~ (r2_relset_1 @ X20 @ X21 @ X19 @ X22))),
% 1.00/1.18      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.00/1.18  thf('23', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.00/1.18             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ X0)
% 1.00/1.18          | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) = (X0))
% 1.00/1.18          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.00/1.18      inference('sup-', [status(thm)], ['21', '22'])).
% 1.00/1.18  thf('24', plain,
% 1.00/1.18      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.00/1.18        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) = (sk_B)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['12', '23'])).
% 1.00/1.18  thf('25', plain,
% 1.00/1.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('26', plain,
% 1.00/1.18      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) = (sk_B))),
% 1.00/1.18      inference('demod', [status(thm)], ['24', '25'])).
% 1.00/1.18  thf('27', plain, (((sk_B) = (k5_relat_1 @ sk_C @ sk_B))),
% 1.00/1.18      inference('demod', [status(thm)], ['10', '11', '26'])).
% 1.00/1.18  thf(dt_k2_funct_1, axiom,
% 1.00/1.18    (![A:$i]:
% 1.00/1.18     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.00/1.18       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.00/1.18         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.00/1.18  thf('28', plain,
% 1.00/1.18      (![X11 : $i]:
% 1.00/1.18         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 1.00/1.18          | ~ (v1_funct_1 @ X11)
% 1.00/1.18          | ~ (v1_relat_1 @ X11))),
% 1.00/1.18      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.00/1.18  thf(t55_relat_1, axiom,
% 1.00/1.18    (![A:$i]:
% 1.00/1.18     ( ( v1_relat_1 @ A ) =>
% 1.00/1.18       ( ![B:$i]:
% 1.00/1.18         ( ( v1_relat_1 @ B ) =>
% 1.00/1.18           ( ![C:$i]:
% 1.00/1.18             ( ( v1_relat_1 @ C ) =>
% 1.00/1.18               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.00/1.18                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.00/1.18  thf('29', plain,
% 1.00/1.18      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ X6)
% 1.00/1.18          | ((k5_relat_1 @ (k5_relat_1 @ X7 @ X6) @ X8)
% 1.00/1.18              = (k5_relat_1 @ X7 @ (k5_relat_1 @ X6 @ X8)))
% 1.00/1.18          | ~ (v1_relat_1 @ X8)
% 1.00/1.18          | ~ (v1_relat_1 @ X7))),
% 1.00/1.18      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.00/1.18  thf('30', plain,
% 1.00/1.18      (![X12 : $i]:
% 1.00/1.18         (~ (v2_funct_1 @ X12)
% 1.00/1.18          | ((k5_relat_1 @ X12 @ (k2_funct_1 @ X12))
% 1.00/1.18              = (k6_partfun1 @ (k1_relat_1 @ X12)))
% 1.00/1.18          | ~ (v1_funct_1 @ X12)
% 1.00/1.18          | ~ (v1_relat_1 @ X12))),
% 1.00/1.18      inference('demod', [status(thm)], ['1', '2'])).
% 1.00/1.18  thf('31', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         (((k5_relat_1 @ X1 @ 
% 1.00/1.18            (k5_relat_1 @ X0 @ (k2_funct_1 @ (k5_relat_1 @ X1 @ X0))))
% 1.00/1.18            = (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))
% 1.00/1.18          | ~ (v1_relat_1 @ X1)
% 1.00/1.18          | ~ (v1_relat_1 @ (k2_funct_1 @ (k5_relat_1 @ X1 @ X0)))
% 1.00/1.18          | ~ (v1_relat_1 @ X0)
% 1.00/1.18          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.00/1.18          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 1.00/1.18          | ~ (v2_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 1.00/1.18      inference('sup+', [status(thm)], ['29', '30'])).
% 1.00/1.18  thf('32', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.00/1.18          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 1.00/1.18          | ~ (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 1.00/1.18          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 1.00/1.18          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 1.00/1.18          | ~ (v1_relat_1 @ X0)
% 1.00/1.18          | ~ (v1_relat_1 @ X1)
% 1.00/1.18          | ((k5_relat_1 @ X1 @ 
% 1.00/1.18              (k5_relat_1 @ X0 @ (k2_funct_1 @ (k5_relat_1 @ X1 @ X0))))
% 1.00/1.18              = (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0)))))),
% 1.00/1.18      inference('sup-', [status(thm)], ['28', '31'])).
% 1.00/1.18  thf('33', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         (((k5_relat_1 @ X1 @ 
% 1.00/1.18            (k5_relat_1 @ X0 @ (k2_funct_1 @ (k5_relat_1 @ X1 @ X0))))
% 1.00/1.18            = (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ X1 @ X0))))
% 1.00/1.18          | ~ (v1_relat_1 @ X1)
% 1.00/1.18          | ~ (v1_relat_1 @ X0)
% 1.00/1.18          | ~ (v2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 1.00/1.18          | ~ (v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 1.00/1.18          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 1.00/1.18      inference('simplify', [status(thm)], ['32'])).
% 1.00/1.18  thf('34', plain,
% 1.00/1.18      ((~ (v2_funct_1 @ sk_B)
% 1.00/1.18        | ~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B))
% 1.00/1.18        | ~ (v1_funct_1 @ (k5_relat_1 @ sk_C @ sk_B))
% 1.00/1.18        | ~ (v1_relat_1 @ sk_B)
% 1.00/1.18        | ~ (v1_relat_1 @ sk_C)
% 1.00/1.18        | ((k5_relat_1 @ sk_C @ 
% 1.00/1.18            (k5_relat_1 @ sk_B @ (k2_funct_1 @ (k5_relat_1 @ sk_C @ sk_B))))
% 1.00/1.18            = (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))))),
% 1.00/1.18      inference('sup-', [status(thm)], ['27', '33'])).
% 1.00/1.18  thf('35', plain, ((v2_funct_1 @ sk_B)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('36', plain, (((sk_B) = (k5_relat_1 @ sk_C @ sk_B))),
% 1.00/1.18      inference('demod', [status(thm)], ['10', '11', '26'])).
% 1.00/1.18  thf('37', plain,
% 1.00/1.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf(cc2_relat_1, axiom,
% 1.00/1.18    (![A:$i]:
% 1.00/1.18     ( ( v1_relat_1 @ A ) =>
% 1.00/1.18       ( ![B:$i]:
% 1.00/1.18         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.00/1.18  thf('38', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.00/1.18          | (v1_relat_1 @ X0)
% 1.00/1.18          | ~ (v1_relat_1 @ X1))),
% 1.00/1.18      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.00/1.18  thf('39', plain,
% 1.00/1.18      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 1.00/1.18      inference('sup-', [status(thm)], ['37', '38'])).
% 1.00/1.18  thf(fc6_relat_1, axiom,
% 1.00/1.18    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.00/1.18  thf('40', plain,
% 1.00/1.18      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 1.00/1.18      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.00/1.18  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 1.00/1.18      inference('demod', [status(thm)], ['39', '40'])).
% 1.00/1.18  thf('42', plain, (((sk_B) = (k5_relat_1 @ sk_C @ sk_B))),
% 1.00/1.18      inference('demod', [status(thm)], ['10', '11', '26'])).
% 1.00/1.18  thf('43', plain, ((v1_funct_1 @ sk_B)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('44', plain, ((v1_relat_1 @ sk_B)),
% 1.00/1.18      inference('demod', [status(thm)], ['39', '40'])).
% 1.00/1.18  thf('45', plain,
% 1.00/1.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('46', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.00/1.18          | (v1_relat_1 @ X0)
% 1.00/1.18          | ~ (v1_relat_1 @ X1))),
% 1.00/1.18      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.00/1.18  thf('47', plain,
% 1.00/1.18      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 1.00/1.18      inference('sup-', [status(thm)], ['45', '46'])).
% 1.00/1.18  thf('48', plain,
% 1.00/1.18      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 1.00/1.18      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.00/1.18  thf('49', plain, ((v1_relat_1 @ sk_C)),
% 1.00/1.18      inference('demod', [status(thm)], ['47', '48'])).
% 1.00/1.18  thf('50', plain, (((sk_B) = (k5_relat_1 @ sk_C @ sk_B))),
% 1.00/1.18      inference('demod', [status(thm)], ['10', '11', '26'])).
% 1.00/1.18  thf('51', plain, (((sk_B) = (k5_relat_1 @ sk_C @ sk_B))),
% 1.00/1.18      inference('demod', [status(thm)], ['10', '11', '26'])).
% 1.00/1.18  thf('52', plain,
% 1.00/1.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf(t67_funct_2, axiom,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 1.00/1.18         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 1.00/1.18       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 1.00/1.18  thf('53', plain,
% 1.00/1.18      (![X36 : $i, X37 : $i]:
% 1.00/1.18         (((k1_relset_1 @ X36 @ X36 @ X37) = (X36))
% 1.00/1.18          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))
% 1.00/1.18          | ~ (v1_funct_2 @ X37 @ X36 @ X36)
% 1.00/1.18          | ~ (v1_funct_1 @ X37))),
% 1.00/1.18      inference('cnf', [status(esa)], [t67_funct_2])).
% 1.00/1.18  thf('54', plain,
% 1.00/1.18      ((~ (v1_funct_1 @ sk_B)
% 1.00/1.18        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 1.00/1.18        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['52', '53'])).
% 1.00/1.18  thf('55', plain, ((v1_funct_1 @ sk_B)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('56', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('57', plain,
% 1.00/1.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf(redefinition_k1_relset_1, axiom,
% 1.00/1.18    (![A:$i,B:$i,C:$i]:
% 1.00/1.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.00/1.18       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.00/1.18  thf('58', plain,
% 1.00/1.18      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.00/1.18         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 1.00/1.18          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.00/1.18      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.00/1.18  thf('59', plain,
% 1.00/1.18      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 1.00/1.18      inference('sup-', [status(thm)], ['57', '58'])).
% 1.00/1.18  thf('60', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 1.00/1.18      inference('demod', [status(thm)], ['54', '55', '56', '59'])).
% 1.00/1.18  thf('61', plain,
% 1.00/1.18      (((k5_relat_1 @ sk_C @ (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))
% 1.00/1.18         = (k6_partfun1 @ sk_A))),
% 1.00/1.18      inference('demod', [status(thm)],
% 1.00/1.18                ['34', '35', '36', '41', '42', '43', '44', '49', '50', '51', 
% 1.00/1.18                 '60'])).
% 1.00/1.18  thf('62', plain,
% 1.00/1.18      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 1.00/1.18          = (k6_partfun1 @ sk_A))
% 1.00/1.18        | ~ (v1_relat_1 @ sk_B)
% 1.00/1.18        | ~ (v1_funct_1 @ sk_B)
% 1.00/1.18        | ~ (v2_funct_1 @ sk_B))),
% 1.00/1.18      inference('sup+', [status(thm)], ['3', '61'])).
% 1.00/1.18  thf('63', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 1.00/1.18      inference('demod', [status(thm)], ['54', '55', '56', '59'])).
% 1.00/1.18  thf('64', plain,
% 1.00/1.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf(cc2_relset_1, axiom,
% 1.00/1.18    (![A:$i,B:$i,C:$i]:
% 1.00/1.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.00/1.18       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.00/1.18  thf('65', plain,
% 1.00/1.18      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.00/1.18         ((v5_relat_1 @ X13 @ X15)
% 1.00/1.18          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.00/1.18      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.00/1.18  thf('66', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 1.00/1.18      inference('sup-', [status(thm)], ['64', '65'])).
% 1.00/1.18  thf(d19_relat_1, axiom,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( v1_relat_1 @ B ) =>
% 1.00/1.18       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.00/1.18  thf('67', plain,
% 1.00/1.18      (![X2 : $i, X3 : $i]:
% 1.00/1.18         (~ (v5_relat_1 @ X2 @ X3)
% 1.00/1.18          | (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 1.00/1.18          | ~ (v1_relat_1 @ X2))),
% 1.00/1.18      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.00/1.18  thf('68', plain,
% 1.00/1.18      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A))),
% 1.00/1.18      inference('sup-', [status(thm)], ['66', '67'])).
% 1.00/1.18  thf('69', plain, ((v1_relat_1 @ sk_C)),
% 1.00/1.18      inference('demod', [status(thm)], ['47', '48'])).
% 1.00/1.18  thf('70', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 1.00/1.18      inference('demod', [status(thm)], ['68', '69'])).
% 1.00/1.18  thf(t79_relat_1, axiom,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( v1_relat_1 @ B ) =>
% 1.00/1.18       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 1.00/1.18         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 1.00/1.18  thf('71', plain,
% 1.00/1.18      (![X9 : $i, X10 : $i]:
% 1.00/1.18         (~ (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 1.00/1.18          | ((k5_relat_1 @ X9 @ (k6_relat_1 @ X10)) = (X9))
% 1.00/1.18          | ~ (v1_relat_1 @ X9))),
% 1.00/1.18      inference('cnf', [status(esa)], [t79_relat_1])).
% 1.00/1.18  thf('72', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 1.00/1.18      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.00/1.18  thf('73', plain,
% 1.00/1.18      (![X9 : $i, X10 : $i]:
% 1.00/1.18         (~ (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 1.00/1.18          | ((k5_relat_1 @ X9 @ (k6_partfun1 @ X10)) = (X9))
% 1.00/1.18          | ~ (v1_relat_1 @ X9))),
% 1.00/1.18      inference('demod', [status(thm)], ['71', '72'])).
% 1.00/1.18  thf('74', plain,
% 1.00/1.18      ((~ (v1_relat_1 @ sk_C)
% 1.00/1.18        | ((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_A)) = (sk_C)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['70', '73'])).
% 1.00/1.18  thf('75', plain, ((v1_relat_1 @ sk_C)),
% 1.00/1.18      inference('demod', [status(thm)], ['47', '48'])).
% 1.00/1.18  thf('76', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_A)) = (sk_C))),
% 1.00/1.18      inference('demod', [status(thm)], ['74', '75'])).
% 1.00/1.18  thf('77', plain, ((v1_relat_1 @ sk_B)),
% 1.00/1.18      inference('demod', [status(thm)], ['39', '40'])).
% 1.00/1.18  thf('78', plain, ((v1_funct_1 @ sk_B)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('79', plain, ((v2_funct_1 @ sk_B)),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('80', plain, (((sk_C) = (k6_partfun1 @ sk_A))),
% 1.00/1.18      inference('demod', [status(thm)], ['62', '63', '76', '77', '78', '79'])).
% 1.00/1.18  thf('81', plain,
% 1.00/1.18      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('82', plain,
% 1.00/1.18      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 1.00/1.18         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.00/1.18          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 1.00/1.18          | (r2_relset_1 @ X20 @ X21 @ X19 @ X22)
% 1.00/1.18          | ((X19) != (X22)))),
% 1.00/1.18      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.00/1.18  thf('83', plain,
% 1.00/1.18      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.00/1.18         ((r2_relset_1 @ X20 @ X21 @ X22 @ X22)
% 1.00/1.18          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.00/1.18      inference('simplify', [status(thm)], ['82'])).
% 1.00/1.18  thf('84', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 1.00/1.18      inference('sup-', [status(thm)], ['81', '83'])).
% 1.00/1.18  thf('85', plain, ($false),
% 1.00/1.18      inference('demod', [status(thm)], ['0', '80', '84'])).
% 1.00/1.18  
% 1.00/1.18  % SZS output end Refutation
% 1.00/1.18  
% 1.00/1.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
