%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4lbf6mjxRj

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 312 expanded)
%              Number of leaves         :   21 (  92 expanded)
%              Depth                    :   17
%              Number of atoms          :  710 (3499 expanded)
%              Number of equality atoms :  134 ( 745 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('6',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('8',plain,(
    ! [X7: $i] :
      ( ( r1_xboole_0 @ X7 @ X7 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('9',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['8'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','15'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k5_xboole_0 @ X14 @ ( k5_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('27',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('28',plain,(
    ! [X48: $i,X49: $i] :
      ( ( X49
        = ( k1_tarski @ X48 ) )
      | ( X49 = k1_xboole_0 )
      | ~ ( r1_tarski @ X49 @ ( k1_tarski @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('29',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k3_xboole_0 @ X18 @ X19 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C @ sk_B ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('36',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C )
      = sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('38',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('40',plain,(
    ! [X48: $i,X49: $i] :
      ( ( X49
        = ( k1_tarski @ X48 ) )
      | ( X49 = k1_xboole_0 )
      | ~ ( r1_tarski @ X49 @ ( k1_tarski @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C
      = ( k1_tarski @ sk_A ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_C
      = ( k1_tarski @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('47',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( sk_C
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['47'])).

thf('49',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('50',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('55',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['46','48','56'])).

thf('58',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['45','57'])).

thf('59',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['50'])).

thf('60',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
        = ( k5_xboole_0 @ X0 @ sk_B ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('65',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('66',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ X0 @ sk_B )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64','67'])).

thf('69',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['60','68'])).

thf('70',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['45','57'])).

thf('71',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_C != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['50'])).

thf('73',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['71','72'])).

thf('74',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['59','73'])).

thf('75',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['43','58','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['24','75'])).

thf('77',plain,
    ( ( k1_tarski @ sk_A )
    = sk_C ),
    inference(demod,[status(thm)],['0','76'])).

thf('78',plain,(
    sk_C
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['45','57'])).

thf('79',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['77','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4lbf6mjxRj
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:57:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 190 iterations in 0.079s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.55  thf(t43_zfmisc_1, conjecture,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.55          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.55          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.55          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.55        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.21/0.55             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.55             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.21/0.55             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.21/0.55  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(commutativity_k5_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.21/0.55  thf(t5_boole, axiom,
% 0.21/0.55    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.55  thf('2', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.55  thf('3', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.55  thf(t95_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k3_xboole_0 @ A @ B ) =
% 0.21/0.55       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X18 : $i, X19 : $i]:
% 0.21/0.55         ((k3_xboole_0 @ X18 @ X19)
% 0.21/0.55           = (k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ 
% 0.21/0.55              (k2_xboole_0 @ X18 @ X19)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.21/0.55  thf(t91_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.55       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.55         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.21/0.55           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (![X18 : $i, X19 : $i]:
% 0.21/0.55         ((k3_xboole_0 @ X18 @ X19)
% 0.21/0.55           = (k5_xboole_0 @ X18 @ 
% 0.21/0.55              (k5_xboole_0 @ X19 @ (k2_xboole_0 @ X18 @ X19))))),
% 0.21/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.55           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['3', '6'])).
% 0.21/0.55  thf(t66_xboole_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.21/0.55       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X7 : $i]: ((r1_xboole_0 @ X7 @ X7) | ((X7) != (k1_xboole_0)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.21/0.55  thf('9', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.55      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.55  thf(t17_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 0.21/0.55      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 0.21/0.55      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.21/0.55  thf(t67_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.21/0.55         ( r1_xboole_0 @ B @ C ) ) =>
% 0.21/0.55       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.55         (((X9) = (k1_xboole_0))
% 0.21/0.55          | ~ (r1_tarski @ X9 @ X10)
% 0.21/0.55          | ~ (r1_tarski @ X9 @ X11)
% 0.21/0.55          | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.21/0.55      inference('cnf', [status(esa)], [t67_xboole_1])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (r1_xboole_0 @ X0 @ X2)
% 0.21/0.55          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2)
% 0.21/0.55          | ((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['10', '13'])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['9', '14'])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k1_xboole_0) = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['7', '15'])).
% 0.21/0.55  thf(t92_xboole_1, axiom,
% 0.21/0.55    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.55  thf('17', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ X17) = (k1_xboole_0))),
% 0.21/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.55         ((k5_xboole_0 @ (k5_xboole_0 @ X14 @ X15) @ X16)
% 0.21/0.55           = (k5_xboole_0 @ X14 @ (k5_xboole_0 @ X15 @ X16)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.55           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['17', '18'])).
% 0.21/0.55  thf('20', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['16', '21'])).
% 0.21/0.55  thf('23', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.55  thf('24', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.55  thf('25', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t7_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (![X12 : $i, X13 : $i]: (r1_tarski @ X12 @ (k2_xboole_0 @ X12 @ X13))),
% 0.21/0.55      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.55  thf('27', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.21/0.55      inference('sup+', [status(thm)], ['25', '26'])).
% 0.21/0.55  thf(l3_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (![X48 : $i, X49 : $i]:
% 0.21/0.55         (((X49) = (k1_tarski @ X48))
% 0.21/0.55          | ((X49) = (k1_xboole_0))
% 0.21/0.55          | ~ (r1_tarski @ X49 @ (k1_tarski @ X48)))),
% 0.21/0.55      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.55  thf('30', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      (![X18 : $i, X19 : $i]:
% 0.21/0.55         ((k3_xboole_0 @ X18 @ X19)
% 0.21/0.55           = (k5_xboole_0 @ X18 @ 
% 0.21/0.55              (k5_xboole_0 @ X19 @ (k2_xboole_0 @ X18 @ X19))))),
% 0.21/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (((k3_xboole_0 @ sk_B @ sk_C)
% 0.21/0.55         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C @ (k1_tarski @ sk_A))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['30', '31'])).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      ((((k3_xboole_0 @ sk_B @ sk_C)
% 0.21/0.55          = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C @ sk_B)))
% 0.21/0.55        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['29', '32'])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      ((((k3_xboole_0 @ sk_B @ sk_C) = (sk_C)) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.55      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 0.21/0.55      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.21/0.55  thf('38', plain, (((r1_tarski @ sk_C @ sk_B) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup+', [status(thm)], ['36', '37'])).
% 0.21/0.55  thf('39', plain,
% 0.21/0.55      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.55  thf('40', plain,
% 0.21/0.55      (![X48 : $i, X49 : $i]:
% 0.21/0.55         (((X49) = (k1_tarski @ X48))
% 0.21/0.55          | ((X49) = (k1_xboole_0))
% 0.21/0.55          | ~ (r1_tarski @ X49 @ (k1_tarski @ X48)))),
% 0.21/0.55      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.55  thf('41', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (r1_tarski @ X0 @ sk_B)
% 0.21/0.55          | ((sk_B) = (k1_xboole_0))
% 0.21/0.55          | ((X0) = (k1_xboole_0))
% 0.21/0.55          | ((X0) = (k1_tarski @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.55  thf('42', plain,
% 0.21/0.55      ((((sk_B) = (k1_xboole_0))
% 0.21/0.55        | ((sk_C) = (k1_tarski @ sk_A))
% 0.21/0.55        | ((sk_C) = (k1_xboole_0))
% 0.21/0.55        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['38', '41'])).
% 0.21/0.55  thf('43', plain,
% 0.21/0.55      ((((sk_C) = (k1_xboole_0))
% 0.21/0.55        | ((sk_C) = (k1_tarski @ sk_A))
% 0.21/0.55        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['42'])).
% 0.21/0.55  thf('44', plain,
% 0.21/0.55      ((((sk_B) != (k1_xboole_0)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('45', plain,
% 0.21/0.55      ((((sk_C) != (k1_tarski @ sk_A))) <= (~ (((sk_C) = (k1_tarski @ sk_A))))),
% 0.21/0.55      inference('split', [status(esa)], ['44'])).
% 0.21/0.55  thf('46', plain,
% 0.21/0.55      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.21/0.55      inference('split', [status(esa)], ['44'])).
% 0.21/0.55  thf('47', plain,
% 0.21/0.55      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_tarski @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('48', plain,
% 0.21/0.55      (~ (((sk_C) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.55      inference('split', [status(esa)], ['47'])).
% 0.21/0.55  thf('49', plain,
% 0.21/0.55      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.55  thf('50', plain,
% 0.21/0.55      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C) != (k1_xboole_0)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('51', plain,
% 0.21/0.55      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.55      inference('split', [status(esa)], ['50'])).
% 0.21/0.55  thf('52', plain,
% 0.21/0.55      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.21/0.55         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['49', '51'])).
% 0.21/0.55  thf('53', plain,
% 0.21/0.55      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.55      inference('simplify', [status(thm)], ['52'])).
% 0.21/0.55  thf('54', plain,
% 0.21/0.55      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.21/0.55      inference('split', [status(esa)], ['44'])).
% 0.21/0.55  thf('55', plain,
% 0.21/0.55      ((((sk_B) != (sk_B)))
% 0.21/0.55         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.55  thf('56', plain,
% 0.21/0.55      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['55'])).
% 0.21/0.55  thf('57', plain, (~ (((sk_C) = (k1_tarski @ sk_A)))),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['46', '48', '56'])).
% 0.21/0.55  thf('58', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.21/0.55      inference('simpl_trail', [status(thm)], ['45', '57'])).
% 0.21/0.55  thf('59', plain,
% 0.21/0.55      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.21/0.55      inference('split', [status(esa)], ['50'])).
% 0.21/0.55  thf('60', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('61', plain,
% 0.21/0.55      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.55      inference('simplify', [status(thm)], ['52'])).
% 0.21/0.55  thf('62', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['16', '21'])).
% 0.21/0.55  thf('63', plain,
% 0.21/0.55      ((![X0 : $i]:
% 0.21/0.55          ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ X0 @ sk_B)))
% 0.21/0.55         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['61', '62'])).
% 0.21/0.55  thf('64', plain,
% 0.21/0.55      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.55      inference('simplify', [status(thm)], ['52'])).
% 0.21/0.55  thf('65', plain,
% 0.21/0.55      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.55      inference('simplify', [status(thm)], ['52'])).
% 0.21/0.55  thf('66', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.21/0.55      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.55  thf('67', plain,
% 0.21/0.55      ((![X0 : $i]: ((k5_xboole_0 @ X0 @ sk_B) = (X0)))
% 0.21/0.55         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['65', '66'])).
% 0.21/0.55  thf('68', plain,
% 0.21/0.55      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 0.21/0.55         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.55      inference('demod', [status(thm)], ['63', '64', '67'])).
% 0.21/0.55  thf('69', plain,
% 0.21/0.55      ((((k1_tarski @ sk_A) = (sk_C))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['60', '68'])).
% 0.21/0.55  thf('70', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.21/0.55      inference('simpl_trail', [status(thm)], ['45', '57'])).
% 0.21/0.55  thf('71', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.55      inference('simplify_reflect-', [status(thm)], ['69', '70'])).
% 0.21/0.55  thf('72', plain,
% 0.21/0.55      (~ (((sk_C) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.21/0.55      inference('split', [status(esa)], ['50'])).
% 0.21/0.55  thf('73', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['71', '72'])).
% 0.21/0.55  thf('74', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.55      inference('simpl_trail', [status(thm)], ['59', '73'])).
% 0.21/0.55  thf('75', plain, (((sk_B) = (k1_xboole_0))),
% 0.21/0.55      inference('simplify_reflect-', [status(thm)], ['43', '58', '74'])).
% 0.21/0.55  thf('76', plain, (![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['24', '75'])).
% 0.21/0.55  thf('77', plain, (((k1_tarski @ sk_A) = (sk_C))),
% 0.21/0.55      inference('demod', [status(thm)], ['0', '76'])).
% 0.21/0.55  thf('78', plain, (((sk_C) != (k1_tarski @ sk_A))),
% 0.21/0.55      inference('simpl_trail', [status(thm)], ['45', '57'])).
% 0.21/0.55  thf('79', plain, ($false),
% 0.21/0.55      inference('simplify_reflect-', [status(thm)], ['77', '78'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
