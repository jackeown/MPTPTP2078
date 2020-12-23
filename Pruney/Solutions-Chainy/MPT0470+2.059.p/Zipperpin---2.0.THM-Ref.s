%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wq6LvbZ77q

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:35 EST 2020

% Result     : Theorem 11.20s
% Output     : Refutation 11.20s
% Verified   : 
% Statistics : Number of formulae       :   66 (  87 expanded)
%              Number of leaves         :   19 (  30 expanded)
%              Depth                    :   17
%              Number of atoms          :  663 ( 878 expanded)
%              Number of equality atoms :   45 (  71 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t56_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X18: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ X18 ) @ ( sk_C @ X18 ) ) @ X18 )
      | ( X18 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf(d8_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( C
                  = ( k5_relat_1 @ A @ B ) )
              <=> ! [D: $i,E: $i] :
                    ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                  <=> ? [F: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B )
                        & ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( X10
       != ( k5_relat_1 @ X9 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X14 @ X11 @ X8 @ X9 ) @ X14 ) @ X8 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X14 ) @ X10 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('4',plain,(
    ! [X8: $i,X9: $i,X11: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X14 ) @ ( k5_relat_1 @ X9 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ X14 @ X11 @ X8 @ X9 ) @ X14 ) @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_F_1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ X0 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','14'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t62_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
            = k1_xboole_0 )
          & ( ( k5_relat_1 @ A @ k1_xboole_0 )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_relat_1])).

thf('18',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('22',plain,(
    ! [X18: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ X18 ) @ ( sk_C @ X18 ) ) @ X18 )
      | ( X18 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( X10
       != ( k5_relat_1 @ X9 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ X11 @ ( sk_F_1 @ X14 @ X11 @ X8 @ X9 ) ) @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X14 ) @ X10 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('24',plain,(
    ! [X8: $i,X9: $i,X11: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X11 @ X14 ) @ ( k5_relat_1 @ X9 @ X8 ) )
      | ( r2_hidden @ ( k4_tarski @ X11 @ ( sk_F_1 @ X14 @ X11 @ X8 @ X9 ) ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_F_1 @ ( sk_C @ ( k5_relat_1 @ X1 @ X0 ) ) @ ( sk_B @ ( k5_relat_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X1 )
      | ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['12'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','30'])).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('35',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('40',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['38','39'])).

thf('41',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['19','40'])).

thf('42',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference(simplify,[status(thm)],['44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wq6LvbZ77q
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 11.20/11.39  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 11.20/11.39  % Solved by: fo/fo7.sh
% 11.20/11.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.20/11.39  % done 10102 iterations in 10.936s
% 11.20/11.39  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 11.20/11.39  % SZS output start Refutation
% 11.20/11.39  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 11.20/11.39  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 11.20/11.39  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 11.20/11.39  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 11.20/11.39  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i).
% 11.20/11.39  thf(sk_C_type, type, sk_C: $i > $i).
% 11.20/11.39  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 11.20/11.39  thf(sk_A_type, type, sk_A: $i).
% 11.20/11.39  thf(sk_B_type, type, sk_B: $i > $i).
% 11.20/11.39  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 11.20/11.39  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 11.20/11.39  thf(cc1_relat_1, axiom,
% 11.20/11.39    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 11.20/11.39  thf('0', plain, (![X7 : $i]: ((v1_relat_1 @ X7) | ~ (v1_xboole_0 @ X7))),
% 11.20/11.39      inference('cnf', [status(esa)], [cc1_relat_1])).
% 11.20/11.39  thf(dt_k5_relat_1, axiom,
% 11.20/11.39    (![A:$i,B:$i]:
% 11.20/11.39     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 11.20/11.39       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 11.20/11.39  thf('1', plain,
% 11.20/11.39      (![X16 : $i, X17 : $i]:
% 11.20/11.39         (~ (v1_relat_1 @ X16)
% 11.20/11.39          | ~ (v1_relat_1 @ X17)
% 11.20/11.39          | (v1_relat_1 @ (k5_relat_1 @ X16 @ X17)))),
% 11.20/11.39      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 11.20/11.39  thf(t56_relat_1, axiom,
% 11.20/11.39    (![A:$i]:
% 11.20/11.39     ( ( v1_relat_1 @ A ) =>
% 11.20/11.39       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 11.20/11.39         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 11.20/11.39  thf('2', plain,
% 11.20/11.39      (![X18 : $i]:
% 11.20/11.39         ((r2_hidden @ (k4_tarski @ (sk_B @ X18) @ (sk_C @ X18)) @ X18)
% 11.20/11.39          | ((X18) = (k1_xboole_0))
% 11.20/11.39          | ~ (v1_relat_1 @ X18))),
% 11.20/11.39      inference('cnf', [status(esa)], [t56_relat_1])).
% 11.20/11.39  thf(d8_relat_1, axiom,
% 11.20/11.39    (![A:$i]:
% 11.20/11.39     ( ( v1_relat_1 @ A ) =>
% 11.20/11.39       ( ![B:$i]:
% 11.20/11.39         ( ( v1_relat_1 @ B ) =>
% 11.20/11.39           ( ![C:$i]:
% 11.20/11.39             ( ( v1_relat_1 @ C ) =>
% 11.20/11.39               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 11.20/11.39                 ( ![D:$i,E:$i]:
% 11.20/11.39                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 11.20/11.39                     ( ?[F:$i]:
% 11.20/11.39                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 11.20/11.39                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 11.20/11.39  thf('3', plain,
% 11.20/11.39      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X14 : $i]:
% 11.20/11.39         (~ (v1_relat_1 @ X8)
% 11.20/11.39          | ((X10) != (k5_relat_1 @ X9 @ X8))
% 11.20/11.39          | (r2_hidden @ (k4_tarski @ (sk_F_1 @ X14 @ X11 @ X8 @ X9) @ X14) @ 
% 11.20/11.39             X8)
% 11.20/11.39          | ~ (r2_hidden @ (k4_tarski @ X11 @ X14) @ X10)
% 11.20/11.39          | ~ (v1_relat_1 @ X10)
% 11.20/11.39          | ~ (v1_relat_1 @ X9))),
% 11.20/11.39      inference('cnf', [status(esa)], [d8_relat_1])).
% 11.20/11.39  thf('4', plain,
% 11.20/11.39      (![X8 : $i, X9 : $i, X11 : $i, X14 : $i]:
% 11.20/11.39         (~ (v1_relat_1 @ X9)
% 11.20/11.39          | ~ (v1_relat_1 @ (k5_relat_1 @ X9 @ X8))
% 11.20/11.39          | ~ (r2_hidden @ (k4_tarski @ X11 @ X14) @ (k5_relat_1 @ X9 @ X8))
% 11.20/11.39          | (r2_hidden @ (k4_tarski @ (sk_F_1 @ X14 @ X11 @ X8 @ X9) @ X14) @ 
% 11.20/11.39             X8)
% 11.20/11.39          | ~ (v1_relat_1 @ X8))),
% 11.20/11.39      inference('simplify', [status(thm)], ['3'])).
% 11.20/11.39  thf('5', plain,
% 11.20/11.39      (![X0 : $i, X1 : $i]:
% 11.20/11.39         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 11.20/11.39          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 11.20/11.39          | ~ (v1_relat_1 @ X0)
% 11.20/11.39          | (r2_hidden @ 
% 11.20/11.39             (k4_tarski @ 
% 11.20/11.39              (sk_F_1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)) @ 
% 11.20/11.39               (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 11.20/11.39              (sk_C @ (k5_relat_1 @ X1 @ X0))) @ 
% 11.20/11.39             X0)
% 11.20/11.39          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 11.20/11.39          | ~ (v1_relat_1 @ X1))),
% 11.20/11.39      inference('sup-', [status(thm)], ['2', '4'])).
% 11.20/11.39  thf('6', plain,
% 11.20/11.39      (![X0 : $i, X1 : $i]:
% 11.20/11.39         (~ (v1_relat_1 @ X1)
% 11.20/11.39          | (r2_hidden @ 
% 11.20/11.39             (k4_tarski @ 
% 11.20/11.39              (sk_F_1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)) @ 
% 11.20/11.39               (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 11.20/11.39              (sk_C @ (k5_relat_1 @ X1 @ X0))) @ 
% 11.20/11.39             X0)
% 11.20/11.39          | ~ (v1_relat_1 @ X0)
% 11.20/11.39          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 11.20/11.39          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 11.20/11.39      inference('simplify', [status(thm)], ['5'])).
% 11.20/11.39  thf('7', plain,
% 11.20/11.39      (![X0 : $i, X1 : $i]:
% 11.20/11.39         (~ (v1_relat_1 @ X0)
% 11.20/11.39          | ~ (v1_relat_1 @ X1)
% 11.20/11.39          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 11.20/11.39          | ~ (v1_relat_1 @ X0)
% 11.20/11.39          | (r2_hidden @ 
% 11.20/11.39             (k4_tarski @ 
% 11.20/11.39              (sk_F_1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)) @ 
% 11.20/11.39               (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 11.20/11.39              (sk_C @ (k5_relat_1 @ X1 @ X0))) @ 
% 11.20/11.39             X0)
% 11.20/11.39          | ~ (v1_relat_1 @ X1))),
% 11.20/11.39      inference('sup-', [status(thm)], ['1', '6'])).
% 11.20/11.39  thf('8', plain,
% 11.20/11.39      (![X0 : $i, X1 : $i]:
% 11.20/11.39         ((r2_hidden @ 
% 11.20/11.39           (k4_tarski @ 
% 11.20/11.39            (sk_F_1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)) @ 
% 11.20/11.39             (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 11.20/11.39            (sk_C @ (k5_relat_1 @ X1 @ X0))) @ 
% 11.20/11.39           X0)
% 11.20/11.39          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 11.20/11.39          | ~ (v1_relat_1 @ X1)
% 11.20/11.39          | ~ (v1_relat_1 @ X0))),
% 11.20/11.39      inference('simplify', [status(thm)], ['7'])).
% 11.20/11.39  thf(t4_boole, axiom,
% 11.20/11.39    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 11.20/11.39  thf('9', plain,
% 11.20/11.39      (![X6 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 11.20/11.39      inference('cnf', [status(esa)], [t4_boole])).
% 11.20/11.39  thf(d5_xboole_0, axiom,
% 11.20/11.39    (![A:$i,B:$i,C:$i]:
% 11.20/11.39     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 11.20/11.39       ( ![D:$i]:
% 11.20/11.39         ( ( r2_hidden @ D @ C ) <=>
% 11.20/11.39           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 11.20/11.39  thf('10', plain,
% 11.20/11.39      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 11.20/11.39         (~ (r2_hidden @ X4 @ X3)
% 11.20/11.39          | ~ (r2_hidden @ X4 @ X2)
% 11.20/11.39          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 11.20/11.39      inference('cnf', [status(esa)], [d5_xboole_0])).
% 11.20/11.39  thf('11', plain,
% 11.20/11.39      (![X1 : $i, X2 : $i, X4 : $i]:
% 11.20/11.39         (~ (r2_hidden @ X4 @ X2)
% 11.20/11.39          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 11.20/11.39      inference('simplify', [status(thm)], ['10'])).
% 11.20/11.39  thf('12', plain,
% 11.20/11.39      (![X0 : $i, X1 : $i]:
% 11.20/11.39         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 11.20/11.39      inference('sup-', [status(thm)], ['9', '11'])).
% 11.20/11.39  thf('13', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 11.20/11.39      inference('condensation', [status(thm)], ['12'])).
% 11.20/11.39  thf('14', plain,
% 11.20/11.39      (![X0 : $i]:
% 11.20/11.39         (~ (v1_relat_1 @ k1_xboole_0)
% 11.20/11.39          | ~ (v1_relat_1 @ X0)
% 11.20/11.39          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 11.20/11.39      inference('sup-', [status(thm)], ['8', '13'])).
% 11.20/11.39  thf('15', plain,
% 11.20/11.39      (![X0 : $i]:
% 11.20/11.39         (~ (v1_xboole_0 @ k1_xboole_0)
% 11.20/11.39          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 11.20/11.39          | ~ (v1_relat_1 @ X0))),
% 11.20/11.39      inference('sup-', [status(thm)], ['0', '14'])).
% 11.20/11.39  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 11.20/11.39  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.20/11.39      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 11.20/11.39  thf('17', plain,
% 11.20/11.39      (![X0 : $i]:
% 11.20/11.39         (((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 11.20/11.39          | ~ (v1_relat_1 @ X0))),
% 11.20/11.39      inference('demod', [status(thm)], ['15', '16'])).
% 11.20/11.39  thf(t62_relat_1, conjecture,
% 11.20/11.39    (![A:$i]:
% 11.20/11.39     ( ( v1_relat_1 @ A ) =>
% 11.20/11.39       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 11.20/11.39         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 11.20/11.39  thf(zf_stmt_0, negated_conjecture,
% 11.20/11.39    (~( ![A:$i]:
% 11.20/11.39        ( ( v1_relat_1 @ A ) =>
% 11.20/11.39          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 11.20/11.39            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 11.20/11.39    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 11.20/11.39  thf('18', plain,
% 11.20/11.39      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 11.20/11.39        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 11.20/11.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.20/11.39  thf('19', plain,
% 11.20/11.39      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 11.20/11.39         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 11.20/11.39      inference('split', [status(esa)], ['18'])).
% 11.20/11.39  thf('20', plain, (![X7 : $i]: ((v1_relat_1 @ X7) | ~ (v1_xboole_0 @ X7))),
% 11.20/11.39      inference('cnf', [status(esa)], [cc1_relat_1])).
% 11.20/11.39  thf('21', plain,
% 11.20/11.39      (![X16 : $i, X17 : $i]:
% 11.20/11.39         (~ (v1_relat_1 @ X16)
% 11.20/11.39          | ~ (v1_relat_1 @ X17)
% 11.20/11.39          | (v1_relat_1 @ (k5_relat_1 @ X16 @ X17)))),
% 11.20/11.39      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 11.20/11.39  thf('22', plain,
% 11.20/11.39      (![X18 : $i]:
% 11.20/11.39         ((r2_hidden @ (k4_tarski @ (sk_B @ X18) @ (sk_C @ X18)) @ X18)
% 11.20/11.39          | ((X18) = (k1_xboole_0))
% 11.20/11.39          | ~ (v1_relat_1 @ X18))),
% 11.20/11.39      inference('cnf', [status(esa)], [t56_relat_1])).
% 11.20/11.39  thf('23', plain,
% 11.20/11.39      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X14 : $i]:
% 11.20/11.39         (~ (v1_relat_1 @ X8)
% 11.20/11.39          | ((X10) != (k5_relat_1 @ X9 @ X8))
% 11.20/11.39          | (r2_hidden @ (k4_tarski @ X11 @ (sk_F_1 @ X14 @ X11 @ X8 @ X9)) @ 
% 11.20/11.39             X9)
% 11.20/11.39          | ~ (r2_hidden @ (k4_tarski @ X11 @ X14) @ X10)
% 11.20/11.39          | ~ (v1_relat_1 @ X10)
% 11.20/11.39          | ~ (v1_relat_1 @ X9))),
% 11.20/11.39      inference('cnf', [status(esa)], [d8_relat_1])).
% 11.20/11.39  thf('24', plain,
% 11.20/11.39      (![X8 : $i, X9 : $i, X11 : $i, X14 : $i]:
% 11.20/11.39         (~ (v1_relat_1 @ X9)
% 11.20/11.39          | ~ (v1_relat_1 @ (k5_relat_1 @ X9 @ X8))
% 11.20/11.39          | ~ (r2_hidden @ (k4_tarski @ X11 @ X14) @ (k5_relat_1 @ X9 @ X8))
% 11.20/11.39          | (r2_hidden @ (k4_tarski @ X11 @ (sk_F_1 @ X14 @ X11 @ X8 @ X9)) @ 
% 11.20/11.39             X9)
% 11.20/11.39          | ~ (v1_relat_1 @ X8))),
% 11.20/11.39      inference('simplify', [status(thm)], ['23'])).
% 11.20/11.39  thf('25', plain,
% 11.20/11.39      (![X0 : $i, X1 : $i]:
% 11.20/11.39         (~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 11.20/11.39          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 11.20/11.39          | ~ (v1_relat_1 @ X0)
% 11.20/11.39          | (r2_hidden @ 
% 11.20/11.39             (k4_tarski @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ 
% 11.20/11.39              (sk_F_1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)) @ 
% 11.20/11.39               (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 11.20/11.39             X1)
% 11.20/11.39          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 11.20/11.39          | ~ (v1_relat_1 @ X1))),
% 11.20/11.39      inference('sup-', [status(thm)], ['22', '24'])).
% 11.20/11.39  thf('26', plain,
% 11.20/11.39      (![X0 : $i, X1 : $i]:
% 11.20/11.39         (~ (v1_relat_1 @ X1)
% 11.20/11.39          | (r2_hidden @ 
% 11.20/11.39             (k4_tarski @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ 
% 11.20/11.39              (sk_F_1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)) @ 
% 11.20/11.39               (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 11.20/11.39             X1)
% 11.20/11.39          | ~ (v1_relat_1 @ X0)
% 11.20/11.39          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 11.20/11.39          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 11.20/11.39      inference('simplify', [status(thm)], ['25'])).
% 11.20/11.39  thf('27', plain,
% 11.20/11.39      (![X0 : $i, X1 : $i]:
% 11.20/11.39         (~ (v1_relat_1 @ X0)
% 11.20/11.39          | ~ (v1_relat_1 @ X1)
% 11.20/11.39          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 11.20/11.39          | ~ (v1_relat_1 @ X0)
% 11.20/11.39          | (r2_hidden @ 
% 11.20/11.39             (k4_tarski @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ 
% 11.20/11.39              (sk_F_1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)) @ 
% 11.20/11.39               (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 11.20/11.39             X1)
% 11.20/11.39          | ~ (v1_relat_1 @ X1))),
% 11.20/11.39      inference('sup-', [status(thm)], ['21', '26'])).
% 11.20/11.39  thf('28', plain,
% 11.20/11.39      (![X0 : $i, X1 : $i]:
% 11.20/11.39         ((r2_hidden @ 
% 11.20/11.39           (k4_tarski @ (sk_B @ (k5_relat_1 @ X1 @ X0)) @ 
% 11.20/11.39            (sk_F_1 @ (sk_C @ (k5_relat_1 @ X1 @ X0)) @ 
% 11.20/11.39             (sk_B @ (k5_relat_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 11.20/11.39           X1)
% 11.20/11.39          | ((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 11.20/11.39          | ~ (v1_relat_1 @ X1)
% 11.20/11.39          | ~ (v1_relat_1 @ X0))),
% 11.20/11.39      inference('simplify', [status(thm)], ['27'])).
% 11.20/11.39  thf('29', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 11.20/11.39      inference('condensation', [status(thm)], ['12'])).
% 11.20/11.39  thf('30', plain,
% 11.20/11.39      (![X0 : $i]:
% 11.20/11.39         (~ (v1_relat_1 @ X0)
% 11.20/11.39          | ~ (v1_relat_1 @ k1_xboole_0)
% 11.20/11.39          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 11.20/11.39      inference('sup-', [status(thm)], ['28', '29'])).
% 11.20/11.39  thf('31', plain,
% 11.20/11.39      (![X0 : $i]:
% 11.20/11.39         (~ (v1_xboole_0 @ k1_xboole_0)
% 11.20/11.39          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 11.20/11.39          | ~ (v1_relat_1 @ X0))),
% 11.20/11.39      inference('sup-', [status(thm)], ['20', '30'])).
% 11.20/11.39  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 11.20/11.39      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 11.20/11.39  thf('33', plain,
% 11.20/11.39      (![X0 : $i]:
% 11.20/11.39         (((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 11.20/11.39          | ~ (v1_relat_1 @ X0))),
% 11.20/11.39      inference('demod', [status(thm)], ['31', '32'])).
% 11.20/11.39  thf('34', plain,
% 11.20/11.39      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 11.20/11.39         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 11.20/11.39      inference('split', [status(esa)], ['18'])).
% 11.20/11.39  thf('35', plain,
% 11.20/11.39      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 11.20/11.39         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 11.20/11.39      inference('sup-', [status(thm)], ['33', '34'])).
% 11.20/11.39  thf('36', plain, ((v1_relat_1 @ sk_A)),
% 11.20/11.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.20/11.39  thf('37', plain,
% 11.20/11.39      ((((k1_xboole_0) != (k1_xboole_0)))
% 11.20/11.39         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 11.20/11.39      inference('demod', [status(thm)], ['35', '36'])).
% 11.20/11.39  thf('38', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 11.20/11.39      inference('simplify', [status(thm)], ['37'])).
% 11.20/11.39  thf('39', plain,
% 11.20/11.39      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 11.20/11.39       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 11.20/11.39      inference('split', [status(esa)], ['18'])).
% 11.20/11.39  thf('40', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 11.20/11.39      inference('sat_resolution*', [status(thm)], ['38', '39'])).
% 11.20/11.39  thf('41', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 11.20/11.39      inference('simpl_trail', [status(thm)], ['19', '40'])).
% 11.20/11.39  thf('42', plain,
% 11.20/11.39      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 11.20/11.39      inference('sup-', [status(thm)], ['17', '41'])).
% 11.20/11.39  thf('43', plain, ((v1_relat_1 @ sk_A)),
% 11.20/11.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.20/11.39  thf('44', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 11.20/11.39      inference('demod', [status(thm)], ['42', '43'])).
% 11.20/11.39  thf('45', plain, ($false), inference('simplify', [status(thm)], ['44'])).
% 11.20/11.39  
% 11.20/11.39  % SZS output end Refutation
% 11.20/11.39  
% 11.20/11.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
