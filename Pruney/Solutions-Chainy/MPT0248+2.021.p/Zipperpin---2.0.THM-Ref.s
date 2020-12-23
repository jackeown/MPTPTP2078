%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2P6n3nramo

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 450 expanded)
%              Number of leaves         :   17 ( 116 expanded)
%              Depth                    :   20
%              Number of atoms          :  660 (5306 expanded)
%              Number of equality atoms :  128 (1210 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k4_xboole_0 @ X5 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('15',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('16',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X30
        = ( k1_tarski @ X29 ) )
      | ( X30 = k1_xboole_0 )
      | ~ ( r1_tarski @ X30 @ ( k1_tarski @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('17',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X30
        = ( k1_tarski @ X29 ) )
      | ( X30 = k1_xboole_0 )
      | ~ ( r1_tarski @ X30 @ ( k1_tarski @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('31',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_C
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['32'])).

thf('35',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('38',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['32'])).

thf('39',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['34','36','40'])).

thf('42',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['33','41'])).

thf('43',plain,
    ( ( sk_C != sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','42'])).

thf('44',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('46',plain,
    ( ( sk_C != sk_C )
   <= ( sk_C != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('49',plain,(
    sk_B
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['47','48'])).

thf('50',plain,(
    sk_B = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['21','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ sk_B ) @ X0 ) ),
    inference(demod,[status(thm)],['12','50'])).

thf('52',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ X11 )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( ( k4_xboole_0 @ X5 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','65'])).

thf('67',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B )
        | ( X0 = sk_B ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    sk_B
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['47','48'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['51','70'])).

thf('72',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['43'])).

thf('74',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('75',plain,
    ( ( sk_B = sk_C )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    sk_B
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['47','48'])).

thf('77',plain,(
    sk_B = sk_C ),
    inference(simpl_trail,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['72','77'])).

thf('79',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B ),
    inference('sup+',[status(thm)],['71','78'])).

thf('80',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['18'])).

thf('81',plain,(
    sk_B
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['47','48'])).

thf('82',plain,(
    sk_B
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['80','81'])).

thf('83',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['79','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2P6n3nramo
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 174 iterations in 0.077s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(d10_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('1', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 0.21/0.53      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.53  thf(l32_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X5 : $i, X7 : $i]:
% 0.21/0.53         (((k4_xboole_0 @ X5 @ X7) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ X7))),
% 0.21/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.53  thf('3', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf(t39_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i]:
% 0.21/0.53         ((k2_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8))
% 0.21/0.53           = (k2_xboole_0 @ X8 @ X9))),
% 0.21/0.53      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.53  thf(t40_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X10 : $i, X11 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 0.21/0.53           = (k4_xboole_0 @ X10 @ X11))),
% 0.21/0.53      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0)
% 0.21/0.53           = (k4_xboole_0 @ X0 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.53  thf('8', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0) = (k1_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X5 : $i, X6 : $i]:
% 0.21/0.53         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.53          | (r1_tarski @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0)),
% 0.21/0.53      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.53  thf(t43_zfmisc_1, conjecture,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.53          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.53          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.53          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.53        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.53             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.53             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.53             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.21/0.53  thf('13', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t7_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.21/0.53      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.53  thf('15', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.21/0.53      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf(l3_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X29 : $i, X30 : $i]:
% 0.21/0.53         (((X30) = (k1_tarski @ X29))
% 0.21/0.53          | ((X30) = (k1_xboole_0))
% 0.21/0.53          | ~ (r1_tarski @ X30 @ (k1_tarski @ X29)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('split', [status(esa)], ['18'])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.21/0.53         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['17', '19'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.53  thf('22', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.53  thf(t46_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (![X15 : $i, X16 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X15 @ (k2_xboole_0 @ X15 @ X16)) = (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['23', '24'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (((k4_xboole_0 @ sk_C @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['22', '25'])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X5 : $i, X6 : $i]:
% 0.21/0.53         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.53        | (r1_tarski @ sk_C @ (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.53  thf('29', plain, ((r1_tarski @ sk_C @ (k1_tarski @ sk_A))),
% 0.21/0.53      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (![X29 : $i, X30 : $i]:
% 0.21/0.53         (((X30) = (k1_tarski @ X29))
% 0.21/0.53          | ((X30) = (k1_xboole_0))
% 0.21/0.53          | ~ (r1_tarski @ X30 @ (k1_tarski @ X29)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      ((((sk_C) = (k1_xboole_0)) | ((sk_C) = (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      ((((sk_B) != (k1_xboole_0)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      ((((sk_C) != (k1_tarski @ sk_A))) <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('split', [status(esa)], ['32'])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.21/0.53      inference('split', [status(esa)], ['32'])).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('split', [status(esa)], ['35'])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.21/0.53      inference('split', [status(esa)], ['32'])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      ((((sk_B) != (sk_B)))
% 0.21/0.53         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.53  thf('41', plain, (~ (((sk_C) = (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['34', '36', '40'])).
% 0.21/0.53  thf('42', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['33', '41'])).
% 0.21/0.53  thf('43', plain, ((((sk_C) != (sk_C)) | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['31', '42'])).
% 0.21/0.53  thf('44', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.21/0.53      inference('split', [status(esa)], ['18'])).
% 0.21/0.53  thf('46', plain, ((((sk_C) != (sk_C))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.53  thf('47', plain, ((((sk_C) = (k1_xboole_0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['46'])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      (~ (((sk_B) = (k1_tarski @ sk_A))) | ~ (((sk_C) = (k1_xboole_0)))),
% 0.21/0.53      inference('split', [status(esa)], ['18'])).
% 0.21/0.53  thf('49', plain, (~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['47', '48'])).
% 0.21/0.53  thf('50', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['21', '49'])).
% 0.21/0.53  thf('51', plain, (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ X0 @ sk_B) @ X0)),
% 0.21/0.53      inference('demod', [status(thm)], ['12', '50'])).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ X0 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['3', '4'])).
% 0.21/0.53  thf('54', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.53  thf('55', plain,
% 0.21/0.53      (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['53', '54'])).
% 0.21/0.53  thf('56', plain,
% 0.21/0.53      (![X10 : $i, X11 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 0.21/0.53           = (k4_xboole_0 @ X10 @ X11))),
% 0.21/0.53      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.21/0.53  thf('57', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0)
% 0.21/0.53           = (k4_xboole_0 @ X0 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['55', '56'])).
% 0.21/0.53  thf('58', plain,
% 0.21/0.53      (![X10 : $i, X11 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ X11)
% 0.21/0.53           = (k4_xboole_0 @ X10 @ X11))),
% 0.21/0.53      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.21/0.53  thf('59', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('60', plain,
% 0.21/0.53      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.21/0.53  thf('61', plain,
% 0.21/0.53      (![X5 : $i, X6 : $i]:
% 0.21/0.53         ((r1_tarski @ X5 @ X6) | ((k4_xboole_0 @ X5 @ X6) != (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.53  thf('62', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.53  thf('63', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.53      inference('simplify', [status(thm)], ['62'])).
% 0.21/0.53  thf('64', plain,
% 0.21/0.53      (![X2 : $i, X4 : $i]:
% 0.21/0.53         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 0.21/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.53  thf('65', plain,
% 0.21/0.53      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.53  thf('66', plain,
% 0.21/0.53      ((![X0 : $i]: (~ (r1_tarski @ X0 @ sk_B) | ((X0) = (k1_xboole_0))))
% 0.21/0.53         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['52', '65'])).
% 0.21/0.53  thf('67', plain,
% 0.21/0.53      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.53  thf('68', plain,
% 0.21/0.53      ((![X0 : $i]: (~ (r1_tarski @ X0 @ sk_B) | ((X0) = (sk_B))))
% 0.21/0.53         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('demod', [status(thm)], ['66', '67'])).
% 0.21/0.53  thf('69', plain, (~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['47', '48'])).
% 0.21/0.53  thf('70', plain, (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_B) | ((X0) = (sk_B)))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['68', '69'])).
% 0.21/0.53  thf('71', plain, (((k2_xboole_0 @ sk_B @ sk_B) = (sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['51', '70'])).
% 0.21/0.53  thf('72', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('73', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.53  thf('74', plain,
% 0.21/0.53      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.53  thf('75', plain,
% 0.21/0.53      ((((sk_B) = (sk_C))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('sup+', [status(thm)], ['73', '74'])).
% 0.21/0.53  thf('76', plain, (~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['47', '48'])).
% 0.21/0.53  thf('77', plain, (((sk_B) = (sk_C))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['75', '76'])).
% 0.21/0.53  thf('78', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['72', '77'])).
% 0.21/0.53  thf('79', plain, (((k1_tarski @ sk_A) = (sk_B))),
% 0.21/0.53      inference('sup+', [status(thm)], ['71', '78'])).
% 0.21/0.53  thf('80', plain,
% 0.21/0.53      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.53      inference('split', [status(esa)], ['18'])).
% 0.21/0.53  thf('81', plain, (~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['47', '48'])).
% 0.21/0.53  thf('82', plain, (((sk_B) != (k1_tarski @ sk_A))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['80', '81'])).
% 0.21/0.53  thf('83', plain, ($false),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['79', '82'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
