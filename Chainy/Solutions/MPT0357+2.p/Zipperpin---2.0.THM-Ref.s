%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0357+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ND2aM6FAZf

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:54 EST 2020

% Result     : Theorem 42.01s
% Output     : Refutation 42.01s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 207 expanded)
%              Number of leaves         :   37 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :  741 (1421 expanded)
%              Number of equality atoms :   71 ( 133 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_8_type,type,(
    sk_B_8: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_20_type,type,(
    sk_C_20: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t36_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( r1_tarski @ ( k3_subset_1 @ ( A @ B ) @ C ) )
           => ( r1_tarski @ ( k3_subset_1 @ ( A @ C ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ A ) ) )
           => ( ( r1_tarski @ ( k3_subset_1 @ ( A @ B ) @ C ) )
             => ( r1_tarski @ ( k3_subset_1 @ ( A @ C ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) @ sk_B_8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ ( sk_C_20 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k3_subset_1 @ ( A @ B ) )
        = ( k4_xboole_0 @ ( A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X1474: $i,X1475: $i] :
      ( ( ( k3_subset_1 @ ( X1474 @ X1475 ) )
        = ( k4_xboole_0 @ ( X1474 @ X1475 ) ) )
      | ~ ( m1_subset_1 @ ( X1475 @ ( k1_zfmisc_1 @ X1474 ) ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ ( A @ B ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('3',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X1474: $i,X1475: $i] :
      ( ( ( k3_subset_1 @ ( X1474 @ X1475 ) )
        = ( k6_subset_1 @ ( X1474 @ X1475 ) ) )
      | ~ ( m1_subset_1 @ ( X1475 @ ( k1_zfmisc_1 @ X1474 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) )
    = ( k6_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( r1_tarski @ ( k6_subset_1 @ ( sk_A_2 @ sk_C_20 ) @ sk_B_8 ) ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    r1_tarski @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ sk_C_20 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( sk_B_8 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X1474: $i,X1475: $i] :
      ( ( ( k3_subset_1 @ ( X1474 @ X1475 ) )
        = ( k6_subset_1 @ ( X1474 @ X1475 ) ) )
      | ~ ( m1_subset_1 @ ( X1475 @ ( k1_zfmisc_1 @ X1474 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('10',plain,
    ( ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) )
    = ( k6_subset_1 @ ( sk_A_2 @ sk_B_8 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k6_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ sk_C_20 ) ),
    inference(demod,[status(thm)],['7','10'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( A @ B ) @ C ) )
     => ( r1_tarski @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('12',plain,(
    ! [X257: $i,X258: $i,X259: $i] :
      ( ( r1_tarski @ ( X257 @ ( k2_xboole_0 @ ( X258 @ X259 ) ) ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ ( X257 @ X258 ) @ X259 ) ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('13',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('14',plain,(
    ! [X257: $i,X258: $i,X259: $i] :
      ( ( r1_tarski @ ( X257 @ ( k2_xboole_0 @ ( X258 @ X259 ) ) ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ ( X257 @ X258 ) @ X259 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_8 @ sk_C_20 ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k3_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('16',plain,(
    ! [X210: $i,X211: $i] :
      ( ( ( k3_xboole_0 @ ( X210 @ X211 ) )
        = X210 )
      | ~ ( r1_tarski @ ( X210 @ X211 ) ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('17',plain,
    ( ( k3_xboole_0 @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_8 @ sk_C_20 ) ) ) )
    = sk_A_2 ),
    inference('sup-',[status(thm)],['15','16'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ ( k3_xboole_0 @ ( A @ B ) ) ) ) ) )).

thf('19',plain,(
    ! [X99: $i,X100: $i] :
      ( ( k5_xboole_0 @ ( X99 @ X100 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ ( X99 @ X100 ) @ ( k3_xboole_0 @ ( X99 @ X100 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('20',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('21',plain,(
    ! [X99: $i,X100: $i] :
      ( ( k5_xboole_0 @ ( X99 @ X100 ) )
      = ( k6_subset_1 @ ( k2_xboole_0 @ ( X99 @ X100 ) @ ( k3_xboole_0 @ ( X99 @ X100 ) ) ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( X0 @ X1 ) )
      = ( k6_subset_1 @ ( k2_xboole_0 @ ( X1 @ X0 ) @ ( k3_xboole_0 @ ( X0 @ X1 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,
    ( ( k5_xboole_0 @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_8 @ sk_C_20 ) ) ) )
    = ( k6_subset_1 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( sk_B_8 @ sk_C_20 ) @ sk_A_2 ) @ sk_A_2 ) ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf(t4_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ C ) )
      = ( k2_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('24',plain,(
    ! [X272: $i,X273: $i,X274: $i] :
      ( ( k2_xboole_0 @ ( k2_xboole_0 @ ( X272 @ X273 ) @ X274 ) )
      = ( k2_xboole_0 @ ( X272 @ ( k2_xboole_0 @ ( X273 @ X274 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_1])).

thf('25',plain,(
    m1_subset_1 @ ( sk_C_20 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('26',plain,(
    ! [X1477: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1477 @ ( k1_zfmisc_1 @ X1477 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('27',plain,(
    ! [X1473: $i] :
      ( ( k2_subset_1 @ X1473 )
      = X1473 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('28',plain,(
    ! [X1477: $i] :
      ( m1_subset_1 @ ( X1477 @ ( k1_zfmisc_1 @ X1477 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X1474: $i,X1475: $i] :
      ( ( ( k3_subset_1 @ ( X1474 @ X1475 ) )
        = ( k6_subset_1 @ ( X1474 @ X1475 ) ) )
      | ~ ( m1_subset_1 @ ( X1475 @ ( k1_zfmisc_1 @ X1474 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( X0 @ X0 ) )
      = ( k6_subset_1 @ ( X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('31',plain,(
    ! [X78: $i,X79: $i] :
      ( ( r1_tarski @ ( X78 @ X79 ) )
      | ( X78 != X79 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X79: $i] :
      ( r1_tarski @ ( X79 @ X79 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('33',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('34',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('35',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( X0 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ ( X0 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( X0 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['30','38'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( r1_tarski @ ( B @ C ) )
          <=> ( r1_tarski @ ( k3_subset_1 @ ( A @ C ) @ ( k3_subset_1 @ ( A @ B ) ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X1555: $i,X1556: $i,X1557: $i] :
      ( ~ ( m1_subset_1 @ ( X1555 @ ( k1_zfmisc_1 @ X1556 ) ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ ( X1556 @ X1555 ) @ ( k3_subset_1 @ ( X1556 @ X1557 ) ) ) )
      | ( r1_tarski @ ( X1557 @ X1555 ) )
      | ~ ( m1_subset_1 @ ( X1557 @ ( k1_zfmisc_1 @ X1556 ) ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( o_0_0_xboole_0 @ ( k3_subset_1 @ ( X1 @ X0 ) ) ) )
      | ~ ( m1_subset_1 @ ( X0 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ( r1_tarski @ ( X0 @ X1 ) )
      | ~ ( m1_subset_1 @ ( X1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ A ) ) )).

thf('42',plain,(
    ! [X216: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ X216 ) ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('43',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('44',plain,(
    ! [X216: $i] :
      ( r1_tarski @ ( o_0_0_xboole_0 @ X216 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X1477: $i] :
      ( m1_subset_1 @ ( X1477 @ ( k1_zfmisc_1 @ X1477 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( X0 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ( r1_tarski @ ( X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['41','44','45'])).

thf('47',plain,(
    r1_tarski @ ( sk_C_20 @ sk_A_2 ) ),
    inference('sup-',[status(thm)],['25','46'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf('48',plain,(
    ! [X161: $i,X162: $i] :
      ( ( ( k2_xboole_0 @ ( X162 @ X161 ) )
        = X161 )
      | ~ ( r1_tarski @ ( X162 @ X161 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('49',plain,
    ( ( k2_xboole_0 @ ( sk_C_20 @ sk_A_2 ) )
    = sk_A_2 ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ ( sk_B_8 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ ( X0 @ ( k1_zfmisc_1 @ X1 ) ) )
      | ( r1_tarski @ ( X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['41','44','45'])).

thf('52',plain,(
    r1_tarski @ ( sk_B_8 @ sk_A_2 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X161: $i,X162: $i] :
      ( ( ( k2_xboole_0 @ ( X162 @ X161 ) )
        = X161 )
      | ~ ( r1_tarski @ ( X162 @ X161 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('54',plain,
    ( ( k2_xboole_0 @ ( sk_B_8 @ sk_A_2 ) )
    = sk_A_2 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ ( X0 @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('56',plain,
    ( ( k5_xboole_0 @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_8 @ sk_C_20 ) ) ) )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['23','24','49','54','55'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ ( A @ A ) )
      = k1_xboole_0 ) )).

thf('57',plain,(
    ! [X402: $i] :
      ( ( k5_xboole_0 @ ( X402 @ X402 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('58',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('59',plain,(
    ! [X402: $i] :
      ( ( k5_xboole_0 @ ( X402 @ X402 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ ( A @ B ) @ C ) )
      = ( k5_xboole_0 @ ( A @ ( k5_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('60',plain,(
    ! [X399: $i,X400: $i,X401: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ ( X399 @ X400 ) @ X401 ) )
      = ( k5_xboole_0 @ ( X399 @ ( k5_xboole_0 @ ( X400 @ X401 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = ( k5_xboole_0 @ ( X1 @ ( k5_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('62',plain,(
    ! [X302: $i] :
      ( ( k5_xboole_0 @ ( X302 @ k1_xboole_0 ) )
      = X302 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('63',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('64',plain,(
    ! [X302: $i] :
      ( ( k5_xboole_0 @ ( X302 @ o_0_0_xboole_0 ) )
      = X302 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k5_xboole_0 @ ( B @ A ) ) ) )).

thf('65',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( X9 @ X8 ) )
      = ( k5_xboole_0 @ ( X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ ( X1 @ ( k5_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['61','66'])).

thf('68',plain,
    ( ( k2_xboole_0 @ ( sk_B_8 @ sk_C_20 ) )
    = ( k5_xboole_0 @ ( sk_A_2 @ o_0_0_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['56','67'])).

thf('69',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( X9 @ X8 ) )
      = ( k5_xboole_0 @ ( X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('71',plain,
    ( ( k2_xboole_0 @ ( sk_B_8 @ sk_C_20 ) )
    = sk_A_2 ),
    inference(demod,[status(thm)],['68','69','70'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ B ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('72',plain,(
    ! [X246: $i,X247: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( X246 @ X247 ) @ X247 ) )
      = ( k4_xboole_0 @ ( X246 @ X247 ) ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('73',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('74',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('75',plain,(
    ! [X246: $i,X247: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ ( X246 @ X247 ) @ X247 ) )
      = ( k6_subset_1 @ ( X246 @ X247 ) ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( k6_subset_1 @ ( sk_A_2 @ sk_C_20 ) )
    = ( k6_subset_1 @ ( sk_B_8 @ sk_C_20 ) ) ),
    inference('sup+',[status(thm)],['71','75'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( A @ B ) @ A ) ) )).

thf('77',plain,(
    ! [X235: $i,X236: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( X235 @ X236 ) @ X235 ) ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('78',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('79',plain,(
    ! [X235: $i,X236: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( X235 @ X236 ) @ X235 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['6','76','79'])).

%------------------------------------------------------------------------------
