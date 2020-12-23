%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0828+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OR4TD7TCTe

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:02 EST 2020

% Result     : Theorem 39.87s
% Output     : Refutation 39.87s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 208 expanded)
%              Number of leaves         :   33 (  78 expanded)
%              Depth                    :   13
%              Number of atoms          :  641 (1883 expanded)
%              Number of equality atoms :   44 (  97 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_91_type,type,(
    sk_C_91: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_57_type,type,(
    sk_B_57: $i )).

thf(t31_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( B @ A ) ) ) ) )
     => ( ( r1_tarski @ ( k6_relat_1 @ B @ C ) )
       => ( ( B
            = ( k1_relset_1 @ ( B @ ( A @ C ) ) ) )
          & ( r1_tarski @ ( B @ ( k2_relset_1 @ ( B @ ( A @ C ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( B @ A ) ) ) ) )
       => ( ( r1_tarski @ ( k6_relat_1 @ B @ C ) )
         => ( ( B
              = ( k1_relset_1 @ ( B @ ( A @ C ) ) ) )
            & ( r1_tarski @ ( B @ ( k2_relset_1 @ ( B @ ( A @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_relset_1])).

thf('0',plain,
    ( ( sk_B_57
     != ( k1_relset_1 @ ( sk_B_57 @ ( sk_A_14 @ sk_C_91 ) ) ) )
    | ~ ( r1_tarski @ ( sk_B_57 @ ( k2_relset_1 @ ( sk_B_57 @ ( sk_A_14 @ sk_C_91 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( sk_B_57 @ ( k2_relset_1 @ ( sk_B_57 @ ( sk_A_14 @ sk_C_91 ) ) ) ) )
   <= ~ ( r1_tarski @ ( sk_B_57 @ ( k2_relset_1 @ ( sk_B_57 @ ( sk_A_14 @ sk_C_91 ) ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ ( sk_C_91 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_B_57 @ sk_A_14 ) ) ) ) ),
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
    ( ( k1_relset_1 @ ( sk_B_57 @ ( sk_A_14 @ sk_C_91 ) ) )
    = ( k1_relat_1 @ sk_C_91 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B_57 @ sk_C_91 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( A @ B ) )
           => ( ( r1_tarski @ ( k1_relat_1 @ A @ ( k1_relat_1 @ B ) ) )
              & ( r1_tarski @ ( k2_relat_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X2496: $i,X2497: $i] :
      ( ~ ( v1_relat_1 @ X2496 )
      | ( r1_tarski @ ( k1_relat_1 @ X2497 @ ( k1_relat_1 @ X2496 ) ) )
      | ~ ( r1_tarski @ ( X2497 @ X2496 ) )
      | ~ ( v1_relat_1 @ X2497 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B_57 ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ sk_B_57 ) @ ( k1_relat_1 @ sk_C_91 ) ) )
    | ~ ( v1_relat_1 @ sk_C_91 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('8',plain,(
    ! [X2135: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2135 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('9',plain,(
    ! [X2561: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X2561 ) )
      = X2561 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('10',plain,(
    m1_subset_1 @ ( sk_C_91 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_B_57 @ sk_A_14 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X2039: $i,X2040: $i] :
      ( ~ ( m1_subset_1 @ ( X2039 @ ( k1_zfmisc_1 @ X2040 ) ) )
      | ( v1_relat_1 @ X2039 )
      | ~ ( v1_relat_1 @ X2040 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( sk_B_57 @ sk_A_14 ) ) )
    | ( v1_relat_1 @ sk_C_91 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) )).

thf('13',plain,(
    ! [X2178: $i,X2179: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ ( X2178 @ X2179 ) ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ sk_C_91 ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( sk_B_57 @ ( k1_relat_1 @ sk_C_91 ) ) ),
    inference(demod,[status(thm)],['7','8','9','14'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('16',plain,(
    ! [X78: $i,X80: $i] :
      ( ( X78 = X80 )
      | ~ ( r1_tarski @ ( X80 @ X78 ) )
      | ~ ( r1_tarski @ ( X78 @ X80 ) ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_91 @ sk_B_57 ) )
    | ( ( k1_relat_1 @ sk_C_91 )
      = sk_B_57 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ ( sk_C_91 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_B_57 @ sk_A_14 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( v4_relat_1 @ ( C @ A ) )
        & ( v5_relat_1 @ ( C @ B ) ) ) ) )).

thf('19',plain,(
    ! [X3536: $i,X3537: $i,X3538: $i] :
      ( ( v4_relat_1 @ ( X3536 @ X3537 ) )
      | ~ ( m1_subset_1 @ ( X3536 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X3537 @ X3538 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('20',plain,(
    v4_relat_1 @ ( sk_C_91 @ sk_B_57 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ ( B @ A ) )
      <=> ( r1_tarski @ ( k1_relat_1 @ B @ A ) ) ) ) )).

thf('21',plain,(
    ! [X2085: $i,X2086: $i] :
      ( ~ ( v4_relat_1 @ ( X2085 @ X2086 ) )
      | ( r1_tarski @ ( k1_relat_1 @ X2085 @ X2086 ) )
      | ~ ( v1_relat_1 @ X2085 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_C_91 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_91 @ sk_B_57 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_C_91 ),
    inference(demod,[status(thm)],['12','13'])).

thf('24',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_91 @ sk_B_57 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k1_relat_1 @ sk_C_91 )
    = sk_B_57 ),
    inference(demod,[status(thm)],['17','24'])).

thf('26',plain,
    ( ( k1_relset_1 @ ( sk_B_57 @ ( sk_A_14 @ sk_C_91 ) ) )
    = sk_B_57 ),
    inference(demod,[status(thm)],['4','25'])).

thf('27',plain,
    ( ( sk_B_57
     != ( k1_relset_1 @ ( sk_B_57 @ ( sk_A_14 @ sk_C_91 ) ) ) )
   <= ( sk_B_57
     != ( k1_relset_1 @ ( sk_B_57 @ ( sk_A_14 @ sk_C_91 ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( ( sk_B_57 != sk_B_57 )
   <= ( sk_B_57
     != ( k1_relset_1 @ ( sk_B_57 @ ( sk_A_14 @ sk_C_91 ) ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( sk_B_57
    = ( k1_relset_1 @ ( sk_B_57 @ ( sk_A_14 @ sk_C_91 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ~ ( r1_tarski @ ( sk_B_57 @ ( k2_relset_1 @ ( sk_B_57 @ ( sk_A_14 @ sk_C_91 ) ) ) ) )
    | ( sk_B_57
     != ( k1_relset_1 @ ( sk_B_57 @ ( sk_A_14 @ sk_C_91 ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,(
    ~ ( r1_tarski @ ( sk_B_57 @ ( k2_relset_1 @ ( sk_B_57 @ ( sk_A_14 @ sk_C_91 ) ) ) ) ) ),
    inference('sat_resolution*',[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( r1_tarski @ ( sk_B_57 @ ( k2_relset_1 @ ( sk_B_57 @ ( sk_A_14 @ sk_C_91 ) ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','31'])).

thf('33',plain,(
    m1_subset_1 @ ( sk_C_91 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_B_57 @ sk_A_14 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( k2_relset_1 @ ( A @ ( B @ C ) ) )
        = ( k2_relat_1 @ C ) ) ) )).

thf('34',plain,(
    ! [X3566: $i,X3567: $i,X3568: $i] :
      ( ( ( k2_relset_1 @ ( X3567 @ ( X3568 @ X3566 ) ) )
        = ( k2_relat_1 @ X3566 ) )
      | ~ ( m1_subset_1 @ ( X3566 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X3567 @ X3568 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('35',plain,
    ( ( k2_relset_1 @ ( sk_B_57 @ ( sk_A_14 @ sk_C_91 ) ) )
    = ( k2_relat_1 @ sk_C_91 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k1_relat_1 @ sk_C_91 )
    = sk_B_57 ),
    inference(demod,[status(thm)],['17','24'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('37',plain,(
    ! [X2118: $i] :
      ( ( ( k3_relat_1 @ X2118 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X2118 @ ( k2_relat_1 @ X2118 ) ) ) )
      | ~ ( v1_relat_1 @ X2118 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('38',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('39',plain,(
    ! [X2118: $i] :
      ( ( ( k3_relat_1 @ X2118 )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X2118 @ ( k1_relat_1 @ X2118 ) ) ) )
      | ~ ( v1_relat_1 @ X2118 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k3_relat_1 @ sk_C_91 )
      = ( k2_xboole_0 @ ( k2_relat_1 @ sk_C_91 @ sk_B_57 ) ) )
    | ~ ( v1_relat_1 @ sk_C_91 ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('42',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B_57 @ sk_C_91 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X2496: $i,X2497: $i] :
      ( ~ ( v1_relat_1 @ X2496 )
      | ( r1_tarski @ ( k2_relat_1 @ X2497 @ ( k2_relat_1 @ X2496 ) ) )
      | ~ ( r1_tarski @ ( X2497 @ X2496 ) )
      | ~ ( v1_relat_1 @ X2497 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B_57 ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ sk_B_57 ) @ ( k2_relat_1 @ sk_C_91 ) ) )
    | ~ ( v1_relat_1 @ sk_C_91 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X2135: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2135 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('46',plain,(
    ! [X2562: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X2562 ) )
      = X2562 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('47',plain,(
    v1_relat_1 @ sk_C_91 ),
    inference(demod,[status(thm)],['12','13'])).

thf('48',plain,(
    r1_tarski @ ( sk_B_57 @ ( k2_relat_1 @ sk_C_91 ) ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf('49',plain,(
    ! [X161: $i,X162: $i] :
      ( ( ( k2_xboole_0 @ ( X162 @ X161 ) )
        = X161 )
      | ~ ( r1_tarski @ ( X162 @ X161 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('50',plain,
    ( ( k2_xboole_0 @ ( sk_B_57 @ ( k2_relat_1 @ sk_C_91 ) ) )
    = ( k2_relat_1 @ sk_C_91 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C_91 ),
    inference(demod,[status(thm)],['12','13'])).

thf('52',plain,
    ( ( k3_relat_1 @ sk_C_91 )
    = ( k2_relat_1 @ sk_C_91 ) ),
    inference(demod,[status(thm)],['40','41','50','51'])).

thf('53',plain,
    ( ( k2_relset_1 @ ( sk_B_57 @ ( sk_A_14 @ sk_C_91 ) ) )
    = ( k3_relat_1 @ sk_C_91 ) ),
    inference(demod,[status(thm)],['35','52'])).

thf('54',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B_57 @ sk_C_91 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( A @ B ) )
           => ( r1_tarski @ ( k3_relat_1 @ A @ ( k3_relat_1 @ B ) ) ) ) ) ) )).

thf('55',plain,(
    ! [X2507: $i,X2508: $i] :
      ( ~ ( v1_relat_1 @ X2507 )
      | ( r1_tarski @ ( k3_relat_1 @ X2508 @ ( k3_relat_1 @ X2507 ) ) )
      | ~ ( r1_tarski @ ( X2508 @ X2507 ) )
      | ~ ( v1_relat_1 @ X2508 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B_57 ) )
    | ( r1_tarski @ ( k3_relat_1 @ ( k6_relat_1 @ sk_B_57 ) @ ( k3_relat_1 @ sk_C_91 ) ) )
    | ~ ( v1_relat_1 @ sk_C_91 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X2135: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2135 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('58',plain,(
    ! [X2562: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X2562 ) )
      = X2562 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('59',plain,(
    ! [X2118: $i] :
      ( ( ( k3_relat_1 @ X2118 )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X2118 @ ( k1_relat_1 @ X2118 ) ) ) )
      | ~ ( v1_relat_1 @ X2118 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k3_relat_1 @ ( k6_relat_1 @ X0 ) )
        = ( k2_xboole_0 @ ( X0 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X2561: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X2561 ) )
      = X2561 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ A ) )
      = A ) )).

thf('62',plain,(
    ! [X43: $i] :
      ( ( k2_xboole_0 @ ( X43 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('63',plain,(
    ! [X2135: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2135 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k3_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_C_91 ),
    inference(demod,[status(thm)],['12','13'])).

thf('66',plain,(
    r1_tarski @ ( sk_B_57 @ ( k3_relat_1 @ sk_C_91 ) ) ),
    inference(demod,[status(thm)],['56','57','64','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['32','53','66'])).

%------------------------------------------------------------------------------
