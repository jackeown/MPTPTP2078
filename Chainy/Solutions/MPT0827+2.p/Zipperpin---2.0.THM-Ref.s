%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0827+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ltovym9ncT

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:01 EST 2020

% Result     : Theorem 40.57s
% Output     : Refutation 40.57s
% Verified   : 
% Statistics : Number of formulae       :   56 (  83 expanded)
%              Number of leaves         :   22 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :  347 ( 789 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_57_type,type,(
    sk_B_57: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_91_type,type,(
    sk_C_91: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_78_type,type,(
    sk_D_78: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t30_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ ( D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( r1_tarski @ ( k6_relat_1 @ C @ D ) )
       => ( ( r1_tarski @ ( C @ ( k1_relset_1 @ ( A @ ( B @ D ) ) ) ) )
          & ( r1_tarski @ ( C @ ( k2_relset_1 @ ( A @ ( B @ D ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ ( D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
       => ( ( r1_tarski @ ( k6_relat_1 @ C @ D ) )
         => ( ( r1_tarski @ ( C @ ( k1_relset_1 @ ( A @ ( B @ D ) ) ) ) )
            & ( r1_tarski @ ( C @ ( k2_relset_1 @ ( A @ ( B @ D ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_relset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ ( sk_C_91 @ ( k1_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_D_78 ) ) ) ) )
    | ~ ( r1_tarski @ ( sk_C_91 @ ( k2_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_D_78 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( sk_C_91 @ ( k2_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_D_78 ) ) ) ) )
   <= ~ ( r1_tarski @ ( sk_C_91 @ ( k2_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_D_78 ) ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ ( sk_D_78 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_57 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( k1_relset_1 @ ( A @ ( B @ C ) ) )
        = ( k1_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X3563: $i,X3564: $i,X3565: $i] :
      ( ( ( k1_relset_1 @ ( X3564 @ ( X3565 @ X3563 ) ) )
        = ( k1_relat_1 @ X3563 ) )
      | ~ ( m1_subset_1 @ ( X3563 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X3564 @ X3565 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('4',plain,
    ( ( k1_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_D_78 ) ) )
    = ( k1_relat_1 @ sk_D_78 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( r1_tarski @ ( sk_C_91 @ ( k1_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_D_78 ) ) ) ) )
   <= ~ ( r1_tarski @ ( sk_C_91 @ ( k1_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_D_78 ) ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('6',plain,
    ( ~ ( r1_tarski @ ( sk_C_91 @ ( k1_relat_1 @ sk_D_78 ) ) )
   <= ~ ( r1_tarski @ ( sk_C_91 @ ( k1_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_D_78 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_C_91 @ sk_D_78 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( A @ B ) )
           => ( ( r1_tarski @ ( k1_relat_1 @ A @ ( k1_relat_1 @ B ) ) )
              & ( r1_tarski @ ( k2_relat_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X2496: $i,X2497: $i] :
      ( ~ ( v1_relat_1 @ X2496 )
      | ( r1_tarski @ ( k1_relat_1 @ X2497 @ ( k1_relat_1 @ X2496 ) ) )
      | ~ ( r1_tarski @ ( X2497 @ X2496 ) )
      | ~ ( v1_relat_1 @ X2497 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C_91 ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ sk_C_91 ) @ ( k1_relat_1 @ sk_D_78 ) ) )
    | ~ ( v1_relat_1 @ sk_D_78 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('10',plain,(
    ! [X2135: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2135 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('11',plain,(
    ! [X2561: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X2561 ) )
      = X2561 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('12',plain,(
    m1_subset_1 @ ( sk_D_78 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_57 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X2039: $i,X2040: $i] :
      ( ~ ( m1_subset_1 @ ( X2039 @ ( k1_zfmisc_1 @ X2040 ) ) )
      | ( v1_relat_1 @ X2039 )
      | ~ ( v1_relat_1 @ X2040 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_57 ) ) )
    | ( v1_relat_1 @ sk_D_78 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) )).

thf('15',plain,(
    ! [X2178: $i,X2179: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ ( X2178 @ X2179 ) ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    v1_relat_1 @ sk_D_78 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ ( sk_C_91 @ ( k1_relat_1 @ sk_D_78 ) ) ),
    inference(demod,[status(thm)],['9','10','11','16'])).

thf('18',plain,(
    r1_tarski @ ( sk_C_91 @ ( k1_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_D_78 ) ) ) ) ),
    inference(demod,[status(thm)],['6','17'])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( sk_C_91 @ ( k2_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_D_78 ) ) ) ) )
    | ~ ( r1_tarski @ ( sk_C_91 @ ( k1_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_D_78 ) ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,(
    ~ ( r1_tarski @ ( sk_C_91 @ ( k2_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_D_78 ) ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( r1_tarski @ ( sk_C_91 @ ( k2_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_D_78 ) ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','20'])).

thf('22',plain,(
    m1_subset_1 @ ( sk_D_78 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_57 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( k2_relset_1 @ ( A @ ( B @ C ) ) )
        = ( k2_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X3566: $i,X3567: $i,X3568: $i] :
      ( ( ( k2_relset_1 @ ( X3567 @ ( X3568 @ X3566 ) ) )
        = ( k2_relat_1 @ X3566 ) )
      | ~ ( m1_subset_1 @ ( X3566 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X3567 @ X3568 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('24',plain,
    ( ( k2_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_D_78 ) ) )
    = ( k2_relat_1 @ sk_D_78 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_C_91 @ sk_D_78 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X2496: $i,X2497: $i] :
      ( ~ ( v1_relat_1 @ X2496 )
      | ( r1_tarski @ ( k2_relat_1 @ X2497 @ ( k2_relat_1 @ X2496 ) ) )
      | ~ ( r1_tarski @ ( X2497 @ X2496 ) )
      | ~ ( v1_relat_1 @ X2497 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C_91 ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ sk_C_91 ) @ ( k2_relat_1 @ sk_D_78 ) ) )
    | ~ ( v1_relat_1 @ sk_D_78 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X2135: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2135 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('29',plain,(
    ! [X2562: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X2562 ) )
      = X2562 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('30',plain,(
    v1_relat_1 @ sk_D_78 ),
    inference(demod,[status(thm)],['14','15'])).

thf('31',plain,(
    r1_tarski @ ( sk_C_91 @ ( k2_relat_1 @ sk_D_78 ) ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['21','24','31'])).

%------------------------------------------------------------------------------
