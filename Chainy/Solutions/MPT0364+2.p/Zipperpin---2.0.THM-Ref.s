%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0364+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.910PmT2ojt

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:54 EST 2020

% Result     : Theorem 10.34s
% Output     : Refutation 10.34s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 191 expanded)
%              Number of leaves         :   32 (  67 expanded)
%              Depth                    :   15
%              Number of atoms          :  680 (1474 expanded)
%              Number of equality atoms :   43 (  72 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_8_type,type,(
    sk_B_8: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_C_20_type,type,(
    sk_C_20: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t44_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( r1_xboole_0 @ ( B @ ( k3_subset_1 @ ( A @ C ) ) ) )
          <=> ( r1_tarski @ ( B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ A ) ) )
           => ( ( r1_xboole_0 @ ( B @ ( k3_subset_1 @ ( A @ C ) ) ) )
            <=> ( r1_tarski @ ( B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ ( sk_B_8 @ sk_C_20 ) )
    | ~ ( r1_xboole_0 @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( sk_B_8 @ sk_C_20 ) )
   <= ~ ( r1_tarski @ ( sk_B_8 @ sk_C_20 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( sk_B_8 @ sk_C_20 ) )
    | ~ ( r1_xboole_0 @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ B ) ) )).

thf('3',plain,(
    ! [X359: $i,X360: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( X359 @ X360 ) @ X360 ) ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ ( A @ B ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('4',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('5',plain,(
    ! [X359: $i,X360: $i] :
      ( r1_xboole_0 @ ( k6_subset_1 @ ( X359 @ X360 ) @ X360 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
     => ( r1_xboole_0 @ ( B @ A ) ) ) )).

thf('6',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( X47 @ X48 ) )
      | ~ ( r1_xboole_0 @ ( X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( X0 @ ( k6_subset_1 @ ( X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_tarski @ ( sk_B_8 @ sk_C_20 ) )
    | ( r1_xboole_0 @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tarski @ ( sk_B_8 @ sk_C_20 ) )
   <= ( r1_tarski @ ( sk_B_8 @ sk_C_20 ) ) ),
    inference(split,[status(esa)],['8'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( A @ B ) )
        & ( r1_xboole_0 @ ( B @ C ) ) )
     => ( r1_xboole_0 @ ( A @ C ) ) ) )).

thf('10',plain,(
    ! [X310: $i,X311: $i,X312: $i] :
      ( ~ ( r1_tarski @ ( X310 @ X311 ) )
      | ~ ( r1_xboole_0 @ ( X311 @ X312 ) )
      | ( r1_xboole_0 @ ( X310 @ X312 ) ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ ( sk_B_8 @ X0 ) )
        | ~ ( r1_xboole_0 @ ( sk_C_20 @ X0 ) ) )
   <= ( r1_tarski @ ( sk_B_8 @ sk_C_20 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( sk_B_8 @ ( k6_subset_1 @ ( X0 @ sk_C_20 ) ) ) )
   <= ( r1_tarski @ ( sk_B_8 @ sk_C_20 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    m1_subset_1 @ ( sk_C_20 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k3_subset_1 @ ( A @ B ) )
        = ( k4_xboole_0 @ ( A @ B ) ) ) ) )).

thf('14',plain,(
    ! [X1474: $i,X1475: $i] :
      ( ( ( k3_subset_1 @ ( X1474 @ X1475 ) )
        = ( k4_xboole_0 @ ( X1474 @ X1475 ) ) )
      | ~ ( m1_subset_1 @ ( X1475 @ ( k1_zfmisc_1 @ X1474 ) ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('15',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('16',plain,(
    ! [X1474: $i,X1475: $i] :
      ( ( ( k3_subset_1 @ ( X1474 @ X1475 ) )
        = ( k6_subset_1 @ ( X1474 @ X1475 ) ) )
      | ~ ( m1_subset_1 @ ( X1475 @ ( k1_zfmisc_1 @ X1474 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) )
    = ( k6_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,
    ( ~ ( r1_xboole_0 @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ) )
   <= ~ ( r1_xboole_0 @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,
    ( ~ ( r1_xboole_0 @ ( sk_B_8 @ ( k6_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ) )
   <= ~ ( r1_xboole_0 @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r1_xboole_0 @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ) )
    | ~ ( r1_tarski @ ( sk_B_8 @ sk_C_20 ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    ~ ( r1_tarski @ ( sk_B_8 @ sk_C_20 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','20'])).

thf('22',plain,(
    ~ ( r1_tarski @ ( sk_B_8 @ sk_C_20 ) ) ),
    inference(simpl_trail,[status(thm)],['1','21'])).

thf('23',plain,
    ( ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) )
    = ( k6_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('24',plain,
    ( ( r1_xboole_0 @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ) )
   <= ( r1_xboole_0 @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ) ) ),
    inference(split,[status(esa)],['8'])).

thf('25',plain,
    ( ( r1_xboole_0 @ ( sk_B_8 @ ( k6_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ) )
   <= ( r1_xboole_0 @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_xboole_0 @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ) )
    | ( r1_tarski @ ( sk_B_8 @ sk_C_20 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('27',plain,(
    r1_xboole_0 @ ( sk_B_8 @ ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['2','20','26'])).

thf('28',plain,(
    r1_xboole_0 @ ( sk_B_8 @ ( k6_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ) ),
    inference(simpl_trail,[status(thm)],['25','27'])).

thf(t81_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) )
     => ( r1_xboole_0 @ ( B @ ( k4_xboole_0 @ ( A @ C ) ) ) ) ) )).

thf('29',plain,(
    ! [X368: $i,X369: $i,X370: $i] :
      ( ( r1_xboole_0 @ ( X368 @ ( k4_xboole_0 @ ( X369 @ X370 ) ) ) )
      | ~ ( r1_xboole_0 @ ( X369 @ ( k4_xboole_0 @ ( X368 @ X370 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('30',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('31',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('32',plain,(
    ! [X368: $i,X369: $i,X370: $i] :
      ( ( r1_xboole_0 @ ( X368 @ ( k6_subset_1 @ ( X369 @ X370 ) ) ) )
      | ~ ( r1_xboole_0 @ ( X369 @ ( k6_subset_1 @ ( X368 @ X370 ) ) ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    r1_xboole_0 @ ( sk_A_2 @ ( k6_subset_1 @ ( sk_B_8 @ sk_C_20 ) ) ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,(
    m1_subset_1 @ ( sk_B_8 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('35',plain,(
    ! [X1477: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1477 @ ( k1_zfmisc_1 @ X1477 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('36',plain,(
    ! [X1473: $i] :
      ( ( k2_subset_1 @ X1473 )
      = X1473 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('37',plain,(
    ! [X1477: $i] :
      ( m1_subset_1 @ ( X1477 @ ( k1_zfmisc_1 @ X1477 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X1474: $i,X1475: $i] :
      ( ( ( k3_subset_1 @ ( X1474 @ X1475 ) )
        = ( k6_subset_1 @ ( X1474 @ X1475 ) ) )
      | ~ ( m1_subset_1 @ ( X1475 @ ( k1_zfmisc_1 @ X1474 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( X0 @ X0 ) )
      = ( k6_subset_1 @ ( X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('40',plain,(
    ! [X78: $i,X79: $i] :
      ( ( r1_tarski @ ( X78 @ X79 ) )
      | ( X78 != X79 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X79: $i] :
      ( r1_tarski @ ( X79 @ X79 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('42',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('43',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('44',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('45',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k6_subset_1 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ ( X0 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( X0 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['39','46'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( r1_tarski @ ( B @ C ) )
          <=> ( r1_tarski @ ( k3_subset_1 @ ( A @ C ) @ ( k3_subset_1 @ ( A @ B ) ) ) ) ) ) ) )).

thf('48',plain,(
    ! [X1555: $i,X1556: $i,X1557: $i] :
      ( ~ ( m1_subset_1 @ ( X1555 @ ( k1_zfmisc_1 @ X1556 ) ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ ( X1556 @ X1555 ) @ ( k3_subset_1 @ ( X1556 @ X1557 ) ) ) )
      | ( r1_tarski @ ( X1557 @ X1555 ) )
      | ~ ( m1_subset_1 @ ( X1557 @ ( k1_zfmisc_1 @ X1556 ) ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( o_0_0_xboole_0 @ ( k3_subset_1 @ ( X1 @ X0 ) ) ) )
      | ~ ( m1_subset_1 @ ( X0 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ( r1_tarski @ ( X0 @ X1 ) )
      | ~ ( m1_subset_1 @ ( X1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ A ) ) )).

thf('50',plain,(
    ! [X216: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ X216 ) ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('51',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('52',plain,(
    ! [X216: $i] :
      ( r1_tarski @ ( o_0_0_xboole_0 @ X216 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X1477: $i] :
      ( m1_subset_1 @ ( X1477 @ ( k1_zfmisc_1 @ X1477 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( X0 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ( r1_tarski @ ( X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['49','52','53'])).

thf('55',plain,(
    r1_tarski @ ( sk_B_8 @ sk_A_2 ) ),
    inference('sup-',[status(thm)],['34','54'])).

thf('56',plain,(
    ! [X310: $i,X311: $i,X312: $i] :
      ( ~ ( r1_tarski @ ( X310 @ X311 ) )
      | ~ ( r1_xboole_0 @ ( X311 @ X312 ) )
      | ( r1_xboole_0 @ ( X310 @ X312 ) ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( sk_B_8 @ X0 ) )
      | ~ ( r1_xboole_0 @ ( sk_A_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r1_xboole_0 @ ( sk_B_8 @ ( k6_subset_1 @ ( sk_B_8 @ sk_C_20 ) ) ) ),
    inference('sup-',[status(thm)],['33','57'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k3_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 ) ) )).

thf('59',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('60',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('61',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k3_xboole_0 @ ( sk_B_8 @ ( k6_subset_1 @ ( sk_B_8 @ sk_C_20 ) ) ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['58','61'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( A @ B ) @ A ) ) )).

thf('63',plain,(
    ! [X235: $i,X236: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( X235 @ X236 ) @ X235 ) ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('64',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('65',plain,(
    ! [X235: $i,X236: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( X235 @ X236 ) @ X235 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k3_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('66',plain,(
    ! [X210: $i,X211: $i] :
      ( ( ( k3_xboole_0 @ ( X210 @ X211 ) )
        = X210 )
      | ~ ( r1_tarski @ ( X210 @ X211 ) ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k6_subset_1 @ ( X0 @ X1 ) @ X0 ) )
      = ( k6_subset_1 @ ( X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('68',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( X0 @ ( k6_subset_1 @ ( X0 @ X1 ) ) ) )
      = ( k6_subset_1 @ ( X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k6_subset_1 @ ( sk_B_8 @ sk_C_20 ) )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['62','69'])).

thf('71',plain,(
    ! [X88: $i,X89: $i] :
      ( ( r1_tarski @ ( X88 @ X89 ) )
      | ( ( k4_xboole_0 @ ( X88 @ X89 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('72',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('73',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('74',plain,(
    ! [X88: $i,X89: $i] :
      ( ( r1_tarski @ ( X88 @ X89 ) )
      | ( ( k6_subset_1 @ ( X88 @ X89 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( r1_tarski @ ( sk_B_8 @ sk_C_20 ) ) ),
    inference('sup-',[status(thm)],['70','74'])).

thf('76',plain,(
    r1_tarski @ ( sk_B_8 @ sk_C_20 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['22','76'])).

%------------------------------------------------------------------------------
