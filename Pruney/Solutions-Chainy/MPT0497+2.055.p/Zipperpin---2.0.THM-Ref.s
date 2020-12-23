%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Jb7t2gbRAx

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:13 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 275 expanded)
%              Number of leaves         :   22 (  83 expanded)
%              Depth                    :   23
%              Number of atoms          :  887 (2508 expanded)
%              Number of equality atoms :   80 ( 260 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t95_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( ( k7_relat_1 @ B @ A )
            = k1_xboole_0 )
        <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_relat_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
      = ( k1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,
    ( ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('9',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['8','13'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X21 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('17',plain,(
    ! [X17: $i] :
      ( ( ( k1_relat_1 @ X17 )
       != k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k7_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','27'])).

thf('29',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','28'])).

thf('30',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('31',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('32',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','27','31'])).

thf('33',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['30','32'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('36',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ X18 @ ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ X1 ) ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A @ ( k1_relat_1 @ sk_B ) ) @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['33','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 )
       != k1_xboole_0 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X21 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( r2_hidden @ ( sk_C @ sk_A @ ( k1_relat_1 @ sk_B ) ) @ k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['40','51','52'])).

thf('54',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('55',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ( ( k4_xboole_0 @ X8 @ X10 )
       != X8 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('59',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('60',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X21 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('61',plain,
    ( ( ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) )
   <= ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','27','31'])).

thf('65',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','50'])).

thf('67',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('69',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('73',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X21 ) @ X22 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('75',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X19 ) ) )
      | ( r2_hidden @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B ) ) @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','80'])).

thf('82',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_B ) ) @ k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','83'])).

thf('85',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['53','84'])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['29','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Jb7t2gbRAx
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.54/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.77  % Solved by: fo/fo7.sh
% 0.54/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.77  % done 620 iterations in 0.317s
% 0.54/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.77  % SZS output start Refutation
% 0.54/0.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.77  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.54/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.54/0.77  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.54/0.77  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.54/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.54/0.77  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.54/0.77  thf(t95_relat_1, conjecture,
% 0.54/0.77    (![A:$i,B:$i]:
% 0.54/0.77     ( ( v1_relat_1 @ B ) =>
% 0.54/0.77       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.54/0.77         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.54/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.77    (~( ![A:$i,B:$i]:
% 0.54/0.77        ( ( v1_relat_1 @ B ) =>
% 0.54/0.77          ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.54/0.77            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.54/0.77    inference('cnf.neg', [status(esa)], [t95_relat_1])).
% 0.54/0.77  thf('0', plain,
% 0.54/0.77      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.54/0.77        | ((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('1', plain,
% 0.54/0.77      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.54/0.77         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.54/0.77      inference('split', [status(esa)], ['0'])).
% 0.54/0.77  thf('2', plain,
% 0.54/0.77      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.54/0.77       ~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.54/0.77      inference('split', [status(esa)], ['0'])).
% 0.54/0.77  thf('3', plain,
% 0.54/0.77      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.54/0.77        | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('4', plain,
% 0.54/0.77      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.54/0.77         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.54/0.77      inference('split', [status(esa)], ['3'])).
% 0.54/0.77  thf(t83_xboole_1, axiom,
% 0.54/0.77    (![A:$i,B:$i]:
% 0.54/0.77     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.54/0.77  thf('5', plain,
% 0.54/0.77      (![X8 : $i, X9 : $i]:
% 0.54/0.77         (((k4_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.54/0.77      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.54/0.77  thf('6', plain,
% 0.54/0.77      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) = (k1_relat_1 @ sk_B)))
% 0.54/0.77         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['4', '5'])).
% 0.54/0.77  thf(t48_xboole_1, axiom,
% 0.54/0.77    (![A:$i,B:$i]:
% 0.54/0.77     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.54/0.77  thf('7', plain,
% 0.54/0.77      (![X6 : $i, X7 : $i]:
% 0.54/0.77         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.54/0.77           = (k3_xboole_0 @ X6 @ X7))),
% 0.54/0.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.54/0.77  thf('8', plain,
% 0.54/0.77      ((((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_relat_1 @ sk_B))
% 0.54/0.77          = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.54/0.77         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.54/0.77      inference('sup+', [status(thm)], ['6', '7'])).
% 0.54/0.77  thf(t3_boole, axiom,
% 0.54/0.77    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.54/0.77  thf('9', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.54/0.77      inference('cnf', [status(esa)], [t3_boole])).
% 0.54/0.77  thf('10', plain,
% 0.54/0.77      (![X6 : $i, X7 : $i]:
% 0.54/0.77         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.54/0.77           = (k3_xboole_0 @ X6 @ X7))),
% 0.54/0.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.54/0.77  thf('11', plain,
% 0.54/0.77      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.54/0.77      inference('sup+', [status(thm)], ['9', '10'])).
% 0.54/0.77  thf(t2_boole, axiom,
% 0.54/0.77    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.54/0.77  thf('12', plain,
% 0.54/0.77      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.77      inference('cnf', [status(esa)], [t2_boole])).
% 0.54/0.77  thf('13', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.54/0.77      inference('demod', [status(thm)], ['11', '12'])).
% 0.54/0.77  thf('14', plain,
% 0.54/0.77      ((((k1_xboole_0) = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.54/0.77         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.54/0.77      inference('demod', [status(thm)], ['8', '13'])).
% 0.54/0.77  thf(dt_k7_relat_1, axiom,
% 0.54/0.77    (![A:$i,B:$i]:
% 0.54/0.77     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.54/0.77  thf('15', plain,
% 0.54/0.77      (![X15 : $i, X16 : $i]:
% 0.54/0.77         (~ (v1_relat_1 @ X15) | (v1_relat_1 @ (k7_relat_1 @ X15 @ X16)))),
% 0.54/0.77      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.54/0.77  thf(t90_relat_1, axiom,
% 0.54/0.77    (![A:$i,B:$i]:
% 0.54/0.77     ( ( v1_relat_1 @ B ) =>
% 0.54/0.77       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.54/0.77         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.54/0.77  thf('16', plain,
% 0.54/0.77      (![X21 : $i, X22 : $i]:
% 0.54/0.77         (((k1_relat_1 @ (k7_relat_1 @ X21 @ X22))
% 0.54/0.77            = (k3_xboole_0 @ (k1_relat_1 @ X21) @ X22))
% 0.54/0.77          | ~ (v1_relat_1 @ X21))),
% 0.54/0.77      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.54/0.77  thf(t64_relat_1, axiom,
% 0.54/0.77    (![A:$i]:
% 0.54/0.77     ( ( v1_relat_1 @ A ) =>
% 0.54/0.77       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.54/0.77           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.54/0.77         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.54/0.77  thf('17', plain,
% 0.54/0.77      (![X17 : $i]:
% 0.54/0.77         (((k1_relat_1 @ X17) != (k1_xboole_0))
% 0.54/0.77          | ((X17) = (k1_xboole_0))
% 0.54/0.77          | ~ (v1_relat_1 @ X17))),
% 0.54/0.77      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.54/0.77  thf('18', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i]:
% 0.54/0.77         (((k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) != (k1_xboole_0))
% 0.54/0.77          | ~ (v1_relat_1 @ X1)
% 0.54/0.77          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.54/0.77          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['16', '17'])).
% 0.54/0.77  thf('19', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i]:
% 0.54/0.77         (~ (v1_relat_1 @ X1)
% 0.54/0.77          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.54/0.77          | ~ (v1_relat_1 @ X1)
% 0.54/0.77          | ((k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) != (k1_xboole_0)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['15', '18'])).
% 0.54/0.77  thf('20', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i]:
% 0.54/0.77         (((k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) != (k1_xboole_0))
% 0.54/0.77          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.54/0.77          | ~ (v1_relat_1 @ X1))),
% 0.54/0.77      inference('simplify', [status(thm)], ['19'])).
% 0.54/0.77  thf('21', plain,
% 0.54/0.77      (((((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.77         | ~ (v1_relat_1 @ sk_B)
% 0.54/0.77         | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))
% 0.54/0.77         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['14', '20'])).
% 0.54/0.77  thf('22', plain, ((v1_relat_1 @ sk_B)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('23', plain,
% 0.54/0.77      (((((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.77         | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))
% 0.54/0.77         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.54/0.77      inference('demod', [status(thm)], ['21', '22'])).
% 0.54/0.77  thf('24', plain,
% 0.54/0.77      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.54/0.77         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.54/0.77      inference('simplify', [status(thm)], ['23'])).
% 0.54/0.77  thf('25', plain,
% 0.54/0.77      ((((k7_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.54/0.77         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.54/0.77      inference('split', [status(esa)], ['0'])).
% 0.54/0.77  thf('26', plain,
% 0.54/0.77      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.54/0.77         <= (~ (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.54/0.77             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['24', '25'])).
% 0.54/0.77  thf('27', plain,
% 0.54/0.77      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.54/0.77       ~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.54/0.77      inference('simplify', [status(thm)], ['26'])).
% 0.54/0.77  thf('28', plain, (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.54/0.77      inference('sat_resolution*', [status(thm)], ['2', '27'])).
% 0.54/0.77  thf('29', plain, (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.54/0.77      inference('simpl_trail', [status(thm)], ['1', '28'])).
% 0.54/0.77  thf('30', plain,
% 0.54/0.77      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.54/0.77         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.54/0.77      inference('split', [status(esa)], ['3'])).
% 0.54/0.77  thf('31', plain,
% 0.54/0.77      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.54/0.77       ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.54/0.77      inference('split', [status(esa)], ['3'])).
% 0.54/0.77  thf('32', plain, ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.54/0.77      inference('sat_resolution*', [status(thm)], ['2', '27', '31'])).
% 0.54/0.77  thf('33', plain, (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.54/0.77      inference('simpl_trail', [status(thm)], ['30', '32'])).
% 0.54/0.77  thf(t3_xboole_0, axiom,
% 0.54/0.77    (![A:$i,B:$i]:
% 0.54/0.77     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.54/0.77            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.54/0.77       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.54/0.77            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.54/0.77  thf('34', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i]:
% 0.54/0.77         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.54/0.77      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.54/0.77  thf('35', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i]:
% 0.54/0.77         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.54/0.77      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.54/0.77  thf(t86_relat_1, axiom,
% 0.54/0.77    (![A:$i,B:$i,C:$i]:
% 0.54/0.77     ( ( v1_relat_1 @ C ) =>
% 0.54/0.77       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 0.54/0.77         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 0.54/0.77  thf('36', plain,
% 0.54/0.77      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.54/0.77         (~ (r2_hidden @ X18 @ X19)
% 0.54/0.77          | ~ (r2_hidden @ X18 @ (k1_relat_1 @ X20))
% 0.54/0.77          | (r2_hidden @ X18 @ (k1_relat_1 @ (k7_relat_1 @ X20 @ X19)))
% 0.54/0.77          | ~ (v1_relat_1 @ X20))),
% 0.54/0.77      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.54/0.77  thf('37', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.77         ((r1_xboole_0 @ (k1_relat_1 @ X0) @ X1)
% 0.54/0.77          | ~ (v1_relat_1 @ X0)
% 0.54/0.77          | (r2_hidden @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 0.54/0.77             (k1_relat_1 @ (k7_relat_1 @ X0 @ X2)))
% 0.54/0.77          | ~ (r2_hidden @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X2))),
% 0.54/0.77      inference('sup-', [status(thm)], ['35', '36'])).
% 0.54/0.77  thf('38', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i]:
% 0.54/0.77         ((r1_xboole_0 @ (k1_relat_1 @ X1) @ X0)
% 0.54/0.77          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ X1)) @ 
% 0.54/0.77             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.54/0.77          | ~ (v1_relat_1 @ X1)
% 0.54/0.77          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 0.54/0.77      inference('sup-', [status(thm)], ['34', '37'])).
% 0.54/0.77  thf('39', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i]:
% 0.54/0.77         (~ (v1_relat_1 @ X1)
% 0.54/0.77          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ X1)) @ 
% 0.54/0.77             (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.54/0.77          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 0.54/0.77      inference('simplify', [status(thm)], ['38'])).
% 0.54/0.77  thf('40', plain,
% 0.54/0.77      (((r2_hidden @ (sk_C @ sk_A @ (k1_relat_1 @ sk_B)) @ 
% 0.54/0.77         (k1_relat_1 @ k1_xboole_0))
% 0.54/0.77        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.54/0.77        | ~ (v1_relat_1 @ sk_B))),
% 0.54/0.77      inference('sup+', [status(thm)], ['33', '39'])).
% 0.54/0.77  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('42', plain,
% 0.54/0.77      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.77      inference('cnf', [status(esa)], [t2_boole])).
% 0.54/0.77  thf('43', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i]:
% 0.54/0.77         (((k3_xboole_0 @ (k1_relat_1 @ X1) @ X0) != (k1_xboole_0))
% 0.54/0.77          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.54/0.77          | ~ (v1_relat_1 @ X1))),
% 0.54/0.77      inference('simplify', [status(thm)], ['19'])).
% 0.54/0.77  thf('44', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         (((k1_xboole_0) != (k1_xboole_0))
% 0.54/0.77          | ~ (v1_relat_1 @ X0)
% 0.54/0.77          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['42', '43'])).
% 0.54/0.77  thf('45', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         (((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.54/0.77          | ~ (v1_relat_1 @ X0))),
% 0.54/0.77      inference('simplify', [status(thm)], ['44'])).
% 0.54/0.77  thf('46', plain,
% 0.54/0.77      (![X21 : $i, X22 : $i]:
% 0.54/0.77         (((k1_relat_1 @ (k7_relat_1 @ X21 @ X22))
% 0.54/0.77            = (k3_xboole_0 @ (k1_relat_1 @ X21) @ X22))
% 0.54/0.77          | ~ (v1_relat_1 @ X21))),
% 0.54/0.77      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.54/0.77  thf('47', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         (((k1_relat_1 @ k1_xboole_0)
% 0.54/0.77            = (k3_xboole_0 @ (k1_relat_1 @ X0) @ k1_xboole_0))
% 0.54/0.77          | ~ (v1_relat_1 @ X0)
% 0.54/0.77          | ~ (v1_relat_1 @ X0))),
% 0.54/0.77      inference('sup+', [status(thm)], ['45', '46'])).
% 0.54/0.77  thf('48', plain,
% 0.54/0.77      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.77      inference('cnf', [status(esa)], [t2_boole])).
% 0.54/0.77  thf('49', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.54/0.77          | ~ (v1_relat_1 @ X0)
% 0.54/0.77          | ~ (v1_relat_1 @ X0))),
% 0.54/0.77      inference('demod', [status(thm)], ['47', '48'])).
% 0.54/0.77  thf('50', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         (~ (v1_relat_1 @ X0) | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.54/0.77      inference('simplify', [status(thm)], ['49'])).
% 0.54/0.77  thf('51', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.77      inference('sup-', [status(thm)], ['41', '50'])).
% 0.54/0.77  thf('52', plain, ((v1_relat_1 @ sk_B)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('53', plain,
% 0.54/0.77      (((r2_hidden @ (sk_C @ sk_A @ (k1_relat_1 @ sk_B)) @ k1_xboole_0)
% 0.54/0.77        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.54/0.77      inference('demod', [status(thm)], ['40', '51', '52'])).
% 0.54/0.77  thf('54', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.54/0.77      inference('cnf', [status(esa)], [t3_boole])).
% 0.54/0.77  thf('55', plain,
% 0.54/0.77      (![X8 : $i, X10 : $i]:
% 0.54/0.77         ((r1_xboole_0 @ X8 @ X10) | ((k4_xboole_0 @ X8 @ X10) != (X8)))),
% 0.54/0.77      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.54/0.77  thf('56', plain,
% 0.54/0.77      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.54/0.77      inference('sup-', [status(thm)], ['54', '55'])).
% 0.54/0.77  thf('57', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.54/0.77      inference('simplify', [status(thm)], ['56'])).
% 0.54/0.77  thf('58', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i]:
% 0.54/0.77         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.54/0.77      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.54/0.77  thf('59', plain,
% 0.54/0.77      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.54/0.77         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.54/0.77      inference('split', [status(esa)], ['3'])).
% 0.54/0.77  thf('60', plain,
% 0.54/0.77      (![X21 : $i, X22 : $i]:
% 0.54/0.77         (((k1_relat_1 @ (k7_relat_1 @ X21 @ X22))
% 0.54/0.77            = (k3_xboole_0 @ (k1_relat_1 @ X21) @ X22))
% 0.54/0.77          | ~ (v1_relat_1 @ X21))),
% 0.54/0.77      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.54/0.77  thf('61', plain,
% 0.54/0.77      (((((k1_relat_1 @ k1_xboole_0)
% 0.54/0.77           = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.54/0.77         | ~ (v1_relat_1 @ sk_B)))
% 0.54/0.77         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.54/0.77      inference('sup+', [status(thm)], ['59', '60'])).
% 0.54/0.77  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('63', plain,
% 0.54/0.77      ((((k1_relat_1 @ k1_xboole_0)
% 0.54/0.77          = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.54/0.77         <= ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.54/0.77      inference('demod', [status(thm)], ['61', '62'])).
% 0.54/0.77  thf('64', plain, ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.54/0.77      inference('sat_resolution*', [status(thm)], ['2', '27', '31'])).
% 0.54/0.77  thf('65', plain,
% 0.54/0.77      (((k1_relat_1 @ k1_xboole_0) = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.54/0.77      inference('simpl_trail', [status(thm)], ['63', '64'])).
% 0.54/0.77  thf('66', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.77      inference('sup-', [status(thm)], ['41', '50'])).
% 0.54/0.77  thf('67', plain,
% 0.54/0.77      (((k1_xboole_0) = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.54/0.77      inference('demod', [status(thm)], ['65', '66'])).
% 0.54/0.77  thf('68', plain,
% 0.54/0.77      (![X6 : $i, X7 : $i]:
% 0.54/0.77         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.54/0.77           = (k3_xboole_0 @ X6 @ X7))),
% 0.54/0.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.54/0.77  thf('69', plain,
% 0.54/0.77      (![X6 : $i, X7 : $i]:
% 0.54/0.77         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.54/0.77           = (k3_xboole_0 @ X6 @ X7))),
% 0.54/0.77      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.54/0.77  thf('70', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i]:
% 0.54/0.77         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.54/0.77           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.54/0.77      inference('sup+', [status(thm)], ['68', '69'])).
% 0.54/0.77  thf('71', plain,
% 0.54/0.77      (((k4_xboole_0 @ (k1_relat_1 @ sk_B) @ k1_xboole_0)
% 0.54/0.77         = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.54/0.77            (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.54/0.77      inference('sup+', [status(thm)], ['67', '70'])).
% 0.54/0.77  thf('72', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.54/0.77      inference('cnf', [status(esa)], [t3_boole])).
% 0.54/0.77  thf('73', plain,
% 0.54/0.77      (((k1_relat_1 @ sk_B)
% 0.54/0.77         = (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ 
% 0.54/0.77            (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.54/0.77      inference('demod', [status(thm)], ['71', '72'])).
% 0.54/0.77  thf('74', plain,
% 0.54/0.77      (![X21 : $i, X22 : $i]:
% 0.54/0.77         (((k1_relat_1 @ (k7_relat_1 @ X21 @ X22))
% 0.54/0.77            = (k3_xboole_0 @ (k1_relat_1 @ X21) @ X22))
% 0.54/0.77          | ~ (v1_relat_1 @ X21))),
% 0.54/0.77      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.54/0.77  thf('75', plain,
% 0.54/0.77      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.54/0.77         (~ (r2_hidden @ X18 @ (k1_relat_1 @ (k7_relat_1 @ X20 @ X19)))
% 0.54/0.77          | (r2_hidden @ X18 @ X19)
% 0.54/0.77          | ~ (v1_relat_1 @ X20))),
% 0.54/0.77      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.54/0.77  thf('76', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.77         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.54/0.77          | ~ (v1_relat_1 @ X1)
% 0.54/0.77          | ~ (v1_relat_1 @ X1)
% 0.54/0.77          | (r2_hidden @ X2 @ X0))),
% 0.54/0.77      inference('sup-', [status(thm)], ['74', '75'])).
% 0.54/0.77  thf('77', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.77         ((r2_hidden @ X2 @ X0)
% 0.54/0.77          | ~ (v1_relat_1 @ X1)
% 0.54/0.77          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.54/0.77      inference('simplify', [status(thm)], ['76'])).
% 0.54/0.77  thf('78', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.54/0.77          | ~ (v1_relat_1 @ sk_B)
% 0.54/0.77          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['73', '77'])).
% 0.54/0.77  thf('79', plain, ((v1_relat_1 @ sk_B)),
% 0.54/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.77  thf('80', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 0.54/0.77          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.54/0.77      inference('demod', [status(thm)], ['78', '79'])).
% 0.54/0.77  thf('81', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ X0)
% 0.54/0.77          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_B)) @ 
% 0.54/0.77             (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.54/0.77      inference('sup-', [status(thm)], ['58', '80'])).
% 0.54/0.77  thf('82', plain,
% 0.54/0.77      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.54/0.77         (~ (r2_hidden @ X2 @ X0)
% 0.54/0.77          | ~ (r2_hidden @ X2 @ X3)
% 0.54/0.77          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.54/0.77      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.54/0.77  thf('83', plain,
% 0.54/0.77      (![X0 : $i, X1 : $i]:
% 0.54/0.77         ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ X0)
% 0.54/0.77          | ~ (r1_xboole_0 @ (k4_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A) @ X1)
% 0.54/0.77          | ~ (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_B)) @ X1))),
% 0.54/0.77      inference('sup-', [status(thm)], ['81', '82'])).
% 0.54/0.77  thf('84', plain,
% 0.54/0.77      (![X0 : $i]:
% 0.54/0.77         (~ (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_B)) @ k1_xboole_0)
% 0.54/0.77          | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ X0))),
% 0.54/0.77      inference('sup-', [status(thm)], ['57', '83'])).
% 0.54/0.77  thf('85', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.54/0.77      inference('clc', [status(thm)], ['53', '84'])).
% 0.54/0.77  thf('86', plain, ($false), inference('demod', [status(thm)], ['29', '85'])).
% 0.54/0.77  
% 0.54/0.77  % SZS output end Refutation
% 0.54/0.77  
% 0.63/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
