%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0829+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kO3lp6uaNO

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:02 EST 2020

% Result     : Theorem 48.61s
% Output     : Refutation 48.61s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 206 expanded)
%              Number of leaves         :   33 (  77 expanded)
%              Depth                    :   15
%              Number of atoms          :  635 (1870 expanded)
%              Number of equality atoms :   42 (  94 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_91_type,type,(
    sk_C_91: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_57_type,type,(
    sk_B_57: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_14_type,type,(
    sk_A_14: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(t32_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( r1_tarski @ ( k6_relat_1 @ B @ C ) )
       => ( ( r1_tarski @ ( B @ ( k1_relset_1 @ ( A @ ( B @ C ) ) ) ) )
          & ( B
            = ( k2_relset_1 @ ( A @ ( B @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
       => ( ( r1_tarski @ ( k6_relat_1 @ B @ C ) )
         => ( ( r1_tarski @ ( B @ ( k1_relset_1 @ ( A @ ( B @ C ) ) ) ) )
            & ( B
              = ( k2_relset_1 @ ( A @ ( B @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_relset_1])).

thf('0',plain,(
    m1_subset_1 @ ( sk_C_91 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_57 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( k2_relset_1 @ ( A @ ( B @ C ) ) )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X3566: $i,X3567: $i,X3568: $i] :
      ( ( ( k2_relset_1 @ ( X3567 @ ( X3568 @ X3566 ) ) )
        = ( k2_relat_1 @ X3566 ) )
      | ~ ( m1_subset_1 @ ( X3566 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X3567 @ X3568 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_C_91 ) ) )
    = ( k2_relat_1 @ sk_C_91 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X2496: $i,X2497: $i] :
      ( ~ ( v1_relat_1 @ X2496 )
      | ( r1_tarski @ ( k2_relat_1 @ X2497 @ ( k2_relat_1 @ X2496 ) ) )
      | ~ ( r1_tarski @ ( X2497 @ X2496 ) )
      | ~ ( v1_relat_1 @ X2497 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B_57 ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ sk_B_57 ) @ ( k2_relat_1 @ sk_C_91 ) ) )
    | ~ ( v1_relat_1 @ sk_C_91 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('6',plain,(
    ! [X2135: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2135 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('7',plain,(
    ! [X2562: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X2562 ) )
      = X2562 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('8',plain,(
    m1_subset_1 @ ( sk_C_91 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_57 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('9',plain,(
    ! [X2039: $i,X2040: $i] :
      ( ~ ( m1_subset_1 @ ( X2039 @ ( k1_zfmisc_1 @ X2040 ) ) )
      | ( v1_relat_1 @ X2039 )
      | ~ ( v1_relat_1 @ X2040 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_57 ) ) )
    | ( v1_relat_1 @ sk_C_91 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) )).

thf('11',plain,(
    ! [X2178: $i,X2179: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ ( X2178 @ X2179 ) ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('12',plain,(
    v1_relat_1 @ sk_C_91 ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ ( sk_B_57 @ ( k2_relat_1 @ sk_C_91 ) ) ),
    inference(demod,[status(thm)],['5','6','7','12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('14',plain,(
    ! [X78: $i,X80: $i] :
      ( ( X78 = X80 )
      | ~ ( r1_tarski @ ( X80 @ X78 ) )
      | ~ ( r1_tarski @ ( X78 @ X80 ) ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_91 @ sk_B_57 ) )
    | ( ( k2_relat_1 @ sk_C_91 )
      = sk_B_57 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ ( sk_C_91 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_57 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( v4_relat_1 @ ( C @ A ) )
        & ( v5_relat_1 @ ( C @ B ) ) ) ) )).

thf('17',plain,(
    ! [X3536: $i,X3537: $i,X3538: $i] :
      ( ( v5_relat_1 @ ( X3536 @ X3538 ) )
      | ~ ( m1_subset_1 @ ( X3536 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X3537 @ X3538 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('18',plain,(
    v5_relat_1 @ ( sk_C_91 @ sk_B_57 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ ( B @ A ) )
      <=> ( r1_tarski @ ( k2_relat_1 @ B @ A ) ) ) ) )).

thf('19',plain,(
    ! [X2087: $i,X2088: $i] :
      ( ~ ( v5_relat_1 @ ( X2087 @ X2088 ) )
      | ( r1_tarski @ ( k2_relat_1 @ X2087 @ X2088 ) )
      | ~ ( v1_relat_1 @ X2087 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_C_91 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_91 @ sk_B_57 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_C_91 ),
    inference(demod,[status(thm)],['10','11'])).

thf('22',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_91 @ sk_B_57 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_relat_1 @ sk_C_91 )
    = sk_B_57 ),
    inference(demod,[status(thm)],['15','22'])).

thf('24',plain,
    ( ( k2_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_C_91 ) ) )
    = sk_B_57 ),
    inference(demod,[status(thm)],['2','23'])).

thf('25',plain,
    ( ~ ( r1_tarski @ ( sk_B_57 @ ( k1_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_C_91 ) ) ) ) )
    | ( sk_B_57
     != ( k2_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_C_91 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_B_57
     != ( k2_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_C_91 ) ) ) )
   <= ( sk_B_57
     != ( k2_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_C_91 ) ) ) ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,(
    m1_subset_1 @ ( sk_C_91 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_A_14 @ sk_B_57 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( k1_relset_1 @ ( A @ ( B @ C ) ) )
        = ( k1_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X3563: $i,X3564: $i,X3565: $i] :
      ( ( ( k1_relset_1 @ ( X3564 @ ( X3565 @ X3563 ) ) )
        = ( k1_relat_1 @ X3563 ) )
      | ~ ( m1_subset_1 @ ( X3563 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X3564 @ X3565 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('29',plain,
    ( ( k1_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_C_91 ) ) )
    = ( k1_relat_1 @ sk_C_91 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_relat_1 @ sk_C_91 )
    = sk_B_57 ),
    inference(demod,[status(thm)],['15','22'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('31',plain,(
    ! [X2118: $i] :
      ( ( ( k3_relat_1 @ X2118 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X2118 @ ( k2_relat_1 @ X2118 ) ) ) )
      | ~ ( v1_relat_1 @ X2118 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('32',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('33',plain,(
    ! [X2118: $i] :
      ( ( ( k3_relat_1 @ X2118 )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X2118 @ ( k1_relat_1 @ X2118 ) ) ) )
      | ~ ( v1_relat_1 @ X2118 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k3_relat_1 @ sk_C_91 )
      = ( k2_xboole_0 @ ( sk_B_57 @ ( k1_relat_1 @ sk_C_91 ) ) ) )
    | ~ ( v1_relat_1 @ sk_C_91 ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B_57 @ sk_C_91 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X2496: $i,X2497: $i] :
      ( ~ ( v1_relat_1 @ X2496 )
      | ( r1_tarski @ ( k1_relat_1 @ X2497 @ ( k1_relat_1 @ X2496 ) ) )
      | ~ ( r1_tarski @ ( X2497 @ X2496 ) )
      | ~ ( v1_relat_1 @ X2497 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B_57 ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ sk_B_57 ) @ ( k1_relat_1 @ sk_C_91 ) ) )
    | ~ ( v1_relat_1 @ sk_C_91 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X2135: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2135 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('39',plain,(
    ! [X2561: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X2561 ) )
      = X2561 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('40',plain,(
    v1_relat_1 @ sk_C_91 ),
    inference(demod,[status(thm)],['10','11'])).

thf('41',plain,(
    r1_tarski @ ( sk_B_57 @ ( k1_relat_1 @ sk_C_91 ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf('42',plain,(
    ! [X161: $i,X162: $i] :
      ( ( ( k2_xboole_0 @ ( X162 @ X161 ) )
        = X161 )
      | ~ ( r1_tarski @ ( X162 @ X161 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('43',plain,
    ( ( k2_xboole_0 @ ( sk_B_57 @ ( k1_relat_1 @ sk_C_91 ) ) )
    = ( k1_relat_1 @ sk_C_91 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C_91 ),
    inference(demod,[status(thm)],['10','11'])).

thf('45',plain,
    ( ( k3_relat_1 @ sk_C_91 )
    = ( k1_relat_1 @ sk_C_91 ) ),
    inference(demod,[status(thm)],['34','43','44'])).

thf('46',plain,
    ( ( k1_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_C_91 ) ) )
    = ( k3_relat_1 @ sk_C_91 ) ),
    inference(demod,[status(thm)],['29','45'])).

thf('47',plain,
    ( ~ ( r1_tarski @ ( sk_B_57 @ ( k1_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_C_91 ) ) ) ) )
   <= ~ ( r1_tarski @ ( sk_B_57 @ ( k1_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_C_91 ) ) ) ) ) ),
    inference(split,[status(esa)],['25'])).

thf('48',plain,
    ( ~ ( r1_tarski @ ( sk_B_57 @ ( k3_relat_1 @ sk_C_91 ) ) )
   <= ~ ( r1_tarski @ ( sk_B_57 @ ( k1_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_C_91 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_B_57 @ sk_C_91 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( A @ B ) )
           => ( r1_tarski @ ( k3_relat_1 @ A @ ( k3_relat_1 @ B ) ) ) ) ) ) )).

thf('50',plain,(
    ! [X2507: $i,X2508: $i] :
      ( ~ ( v1_relat_1 @ X2507 )
      | ( r1_tarski @ ( k3_relat_1 @ X2508 @ ( k3_relat_1 @ X2507 ) ) )
      | ~ ( r1_tarski @ ( X2508 @ X2507 ) )
      | ~ ( v1_relat_1 @ X2508 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B_57 ) )
    | ( r1_tarski @ ( k3_relat_1 @ ( k6_relat_1 @ sk_B_57 ) @ ( k3_relat_1 @ sk_C_91 ) ) )
    | ~ ( v1_relat_1 @ sk_C_91 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X2135: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2135 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('53',plain,(
    ! [X2562: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X2562 ) )
      = X2562 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('54',plain,(
    ! [X2118: $i] :
      ( ( ( k3_relat_1 @ X2118 )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X2118 @ ( k1_relat_1 @ X2118 ) ) ) )
      | ~ ( v1_relat_1 @ X2118 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k3_relat_1 @ ( k6_relat_1 @ X0 ) )
        = ( k2_xboole_0 @ ( X0 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X2561: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X2561 ) )
      = X2561 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ A ) )
      = A ) )).

thf('57',plain,(
    ! [X43: $i] :
      ( ( k2_xboole_0 @ ( X43 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('58',plain,(
    ! [X2135: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X2135 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_C_91 ),
    inference(demod,[status(thm)],['10','11'])).

thf('61',plain,(
    r1_tarski @ ( sk_B_57 @ ( k3_relat_1 @ sk_C_91 ) ) ),
    inference(demod,[status(thm)],['51','52','59','60'])).

thf('62',plain,(
    r1_tarski @ ( sk_B_57 @ ( k1_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_C_91 ) ) ) ) ),
    inference(demod,[status(thm)],['48','61'])).

thf('63',plain,
    ( ( sk_B_57
     != ( k2_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_C_91 ) ) ) )
    | ~ ( r1_tarski @ ( sk_B_57 @ ( k1_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_C_91 ) ) ) ) ) ),
    inference(split,[status(esa)],['25'])).

thf('64',plain,(
    sk_B_57
 != ( k2_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_C_91 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['62','63'])).

thf('65',plain,(
    sk_B_57
 != ( k2_relset_1 @ ( sk_A_14 @ ( sk_B_57 @ sk_C_91 ) ) ) ),
    inference(simpl_trail,[status(thm)],['26','64'])).

thf('66',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['24','65'])).

%------------------------------------------------------------------------------
