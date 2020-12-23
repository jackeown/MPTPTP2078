%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0275+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TSaCQ5citC

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:52 EST 2020

% Result     : Theorem 37.07s
% Output     : Refutation 37.07s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 284 expanded)
%              Number of leaves         :   18 (  86 expanded)
%              Depth                    :   16
%              Number of atoms          :  517 (2386 expanded)
%              Number of equality atoms :   50 ( 255 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_C_10_type,type,(
    sk_C_10: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t73_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ ( A @ B ) @ C ) )
        = k1_xboole_0 )
    <=> ( ( r2_hidden @ ( A @ C ) )
        & ( r2_hidden @ ( B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k4_xboole_0 @ ( k2_tarski @ ( A @ B ) @ C ) )
          = k1_xboole_0 )
      <=> ( ( r2_hidden @ ( A @ C ) )
          & ( r2_hidden @ ( B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ ( sk_B_2 @ sk_C_10 ) )
    | ( ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( sk_B_2 @ sk_C_10 ) )
   <= ( r2_hidden @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ ( A @ B ) )
      = ( k2_tarski @ ( B @ A ) ) ) )).

thf('2',plain,(
    ! [X422: $i,X423: $i] :
      ( ( k2_tarski @ ( X423 @ X422 ) )
      = ( k2_tarski @ ( X422 @ X423 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ A @ ( k2_tarski @ ( A @ B ) ) ) )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X1062: $i,X1063: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X1062 @ ( k2_tarski @ ( X1062 @ X1063 ) ) ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t22_zfmisc_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('4',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('5',plain,(
    ! [X1062: $i,X1063: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X1062 @ ( k2_tarski @ ( X1062 @ X1063 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A @ B ) )
        = k1_xboole_0 )
    <=> ( r2_hidden @ ( A @ B ) ) ) )).

thf('6',plain,(
    ! [X1014: $i,X1015: $i] :
      ( ( r2_hidden @ ( X1014 @ X1015 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1014 @ X1015 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('7',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('8',plain,(
    ! [X1014: $i,X1015: $i] :
      ( ( r2_hidden @ ( X1014 @ X1015 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1014 @ X1015 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( r2_hidden @ ( X1 @ ( k2_tarski @ ( X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( X1 @ ( k2_tarski @ ( X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( X0 @ ( k2_tarski @ ( X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['2','10'])).

thf('12',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_C_10 ) )
    | ( ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('15',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) )
      = o_0_0_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('16',plain,(
    ! [X88: $i,X89: $i] :
      ( ( r1_tarski @ ( X88 @ X89 ) )
      | ( ( k4_xboole_0 @ ( X88 @ X89 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('17',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('18',plain,(
    ! [X88: $i,X89: $i] :
      ( ( r1_tarski @ ( X88 @ X89 ) )
      | ( ( k4_xboole_0 @ ( X88 @ X89 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ A ) )
         => ( r2_hidden @ ( C @ B ) ) ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( X13 @ X14 ) )
      | ( r2_hidden @ ( X13 @ X15 ) )
      | ~ ( r1_tarski @ ( X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( X0 @ sk_C_10 ) )
        | ~ ( r2_hidden @ ( X0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_B_2 @ sk_C_10 ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf('24',plain,
    ( ~ ( r2_hidden @ ( sk_B_2 @ sk_C_10 ) )
    | ~ ( r2_hidden @ ( sk_A_2 @ sk_C_10 ) )
    | ( ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ~ ( r2_hidden @ ( sk_B_2 @ sk_C_10 ) )
   <= ~ ( r2_hidden @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_B_2 @ sk_C_10 ) )
    | ( ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( X1 @ ( k2_tarski @ ( X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( X0 @ sk_C_10 ) )
        | ~ ( r2_hidden @ ( X0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('29',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_C_10 ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ ( sk_A_2 @ sk_C_10 ) )
   <= ~ ( r2_hidden @ ( sk_A_2 @ sk_C_10 ) ) ),
    inference(split,[status(esa)],['24'])).

thf('31',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_C_10 ) )
    | ( ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) )
     != k1_xboole_0 )
    | ~ ( r2_hidden @ ( sk_A_2 @ sk_C_10 ) )
    | ~ ( r2_hidden @ ( sk_B_2 @ sk_C_10 ) ) ),
    inference(split,[status(esa)],['24'])).

thf('33',plain,
    ( ( r2_hidden @ ( sk_B_2 @ sk_C_10 ) )
    | ( ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,(
    r2_hidden @ ( sk_B_2 @ sk_C_10 ) ),
    inference('sat_resolution*',[status(thm)],['26','31','32','33'])).

thf('35',plain,(
    r2_hidden @ ( sk_B_2 @ sk_C_10 ) ),
    inference(simpl_trail,[status(thm)],['1','34'])).

thf('36',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_C_10 ) )
   <= ( r2_hidden @ ( sk_A_2 @ sk_C_10 ) ) ),
    inference(split,[status(esa)],['12'])).

thf('37',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_C_10 ) )
    | ( ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('38',plain,(
    r2_hidden @ ( sk_A_2 @ sk_C_10 ) ),
    inference('sat_resolution*',[status(thm)],['26','31','32','37'])).

thf('39',plain,(
    r2_hidden @ ( sk_A_2 @ sk_C_10 ) ),
    inference(simpl_trail,[status(thm)],['36','38'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ ( A @ B ) @ C ) )
    <=> ( ( r2_hidden @ ( A @ C ) )
        & ( r2_hidden @ ( B @ C ) ) ) ) )).

thf('40',plain,(
    ! [X1105: $i,X1107: $i,X1108: $i] :
      ( ( r1_tarski @ ( k2_tarski @ ( X1105 @ X1107 ) @ X1108 ) )
      | ~ ( r2_hidden @ ( X1107 @ X1108 ) )
      | ~ ( r2_hidden @ ( X1105 @ X1108 ) ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( X0 @ sk_C_10 ) )
      | ( r1_tarski @ ( k2_tarski @ ( X0 @ sk_A_2 ) @ sk_C_10 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ ( k2_tarski @ ( sk_B_2 @ sk_A_2 ) @ sk_C_10 ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,(
    ! [X422: $i,X423: $i] :
      ( ( k2_tarski @ ( X423 @ X422 ) )
      = ( k2_tarski @ ( X422 @ X423 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('44',plain,(
    r1_tarski @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('46',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('47',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('50',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('51',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) )
     != o_0_0_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['26','31','32'])).

thf('53',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ ( sk_A_2 @ sk_B_2 ) @ sk_C_10 ) )
 != o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','53'])).

%------------------------------------------------------------------------------
