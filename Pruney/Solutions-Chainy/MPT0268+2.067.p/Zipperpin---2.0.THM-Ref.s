%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.N2N4aL2u2v

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:01 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 132 expanded)
%              Number of leaves         :   21 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :  574 (1019 expanded)
%              Number of equality atoms :   42 (  79 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t65_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = A )
      <=> ~ ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t65_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
   <= ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('7',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('9',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('10',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X24 ) @ X25 )
      | ~ ( r2_hidden @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','12'])).

thf('14',plain,(
    ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('15',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X26 ) @ X27 )
      | ( r2_hidden @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

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

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('19',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('20',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','26'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('28',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('29',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('30',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('33',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('41',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('43',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('44',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X24 ) @ X25 )
      | ~ ( r2_hidden @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['39','52'])).

thf('54',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('55',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A )
    | ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('56',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['2','12','55'])).

thf('57',plain,(
    ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['54','56'])).

thf('58',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','57'])).

thf('59',plain,(
    r2_hidden @ sk_B_1 @ sk_A ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['14','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.N2N4aL2u2v
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:15:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.58/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.77  % Solved by: fo/fo7.sh
% 0.58/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.77  % done 696 iterations in 0.318s
% 0.58/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.77  % SZS output start Refutation
% 0.58/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.77  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.77  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.58/0.77  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.58/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.77  thf(sk_B_type, type, sk_B: $i > $i).
% 0.58/0.77  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.58/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.77  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.58/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.77  thf(t65_zfmisc_1, conjecture,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.58/0.77       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.58/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.77    (~( ![A:$i,B:$i]:
% 0.58/0.77        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.58/0.77          ( ~( r2_hidden @ B @ A ) ) ) )),
% 0.58/0.77    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 0.58/0.77  thf('0', plain,
% 0.58/0.77      ((~ (r2_hidden @ sk_B_1 @ sk_A)
% 0.58/0.77        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('1', plain,
% 0.58/0.77      ((~ (r2_hidden @ sk_B_1 @ sk_A)) <= (~ ((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.58/0.77      inference('split', [status(esa)], ['0'])).
% 0.58/0.77  thf('2', plain,
% 0.58/0.77      (~ ((r2_hidden @ sk_B_1 @ sk_A)) | 
% 0.58/0.77       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 0.58/0.77      inference('split', [status(esa)], ['0'])).
% 0.58/0.77  thf('3', plain,
% 0.58/0.77      (((r2_hidden @ sk_B_1 @ sk_A)
% 0.58/0.77        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) != (sk_A)))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('4', plain,
% 0.58/0.77      (((r2_hidden @ sk_B_1 @ sk_A)) <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.58/0.77      inference('split', [status(esa)], ['3'])).
% 0.58/0.77  thf('5', plain,
% 0.58/0.77      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))
% 0.58/0.77         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 0.58/0.77      inference('split', [status(esa)], ['0'])).
% 0.58/0.77  thf(t79_xboole_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.58/0.77  thf('6', plain,
% 0.58/0.77      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 0.58/0.77      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.58/0.77  thf('7', plain,
% 0.58/0.77      (((r1_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.58/0.77         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 0.58/0.77      inference('sup+', [status(thm)], ['5', '6'])).
% 0.58/0.77  thf(symmetry_r1_xboole_0, axiom,
% 0.58/0.77    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.58/0.77  thf('8', plain,
% 0.58/0.77      (![X6 : $i, X7 : $i]:
% 0.58/0.77         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 0.58/0.77      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.58/0.77  thf('9', plain,
% 0.58/0.77      (((r1_xboole_0 @ (k1_tarski @ sk_B_1) @ sk_A))
% 0.58/0.77         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['7', '8'])).
% 0.58/0.77  thf(l24_zfmisc_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.58/0.77  thf('10', plain,
% 0.58/0.77      (![X24 : $i, X25 : $i]:
% 0.58/0.77         (~ (r1_xboole_0 @ (k1_tarski @ X24) @ X25) | ~ (r2_hidden @ X24 @ X25))),
% 0.58/0.77      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.58/0.77  thf('11', plain,
% 0.58/0.77      ((~ (r2_hidden @ sk_B_1 @ sk_A))
% 0.58/0.77         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 0.58/0.77      inference('sup-', [status(thm)], ['9', '10'])).
% 0.58/0.77  thf('12', plain,
% 0.58/0.77      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))) | 
% 0.58/0.77       ~ ((r2_hidden @ sk_B_1 @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['4', '11'])).
% 0.58/0.77  thf('13', plain, (~ ((r2_hidden @ sk_B_1 @ sk_A))),
% 0.58/0.77      inference('sat_resolution*', [status(thm)], ['2', '12'])).
% 0.58/0.77  thf('14', plain, (~ (r2_hidden @ sk_B_1 @ sk_A)),
% 0.58/0.77      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.58/0.77  thf(l27_zfmisc_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.58/0.77  thf('15', plain,
% 0.58/0.77      (![X26 : $i, X27 : $i]:
% 0.58/0.77         ((r1_xboole_0 @ (k1_tarski @ X26) @ X27) | (r2_hidden @ X26 @ X27))),
% 0.58/0.77      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.58/0.77  thf('16', plain,
% 0.58/0.77      (![X6 : $i, X7 : $i]:
% 0.58/0.77         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 0.58/0.77      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.58/0.77  thf('17', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i]:
% 0.58/0.77         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['15', '16'])).
% 0.58/0.77  thf(t3_xboole_0, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.58/0.77            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.58/0.77       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.58/0.77            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.58/0.77  thf('18', plain,
% 0.58/0.77      (![X8 : $i, X9 : $i]:
% 0.58/0.77         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 0.58/0.77      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.58/0.77  thf(d4_xboole_0, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i]:
% 0.58/0.77     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.58/0.77       ( ![D:$i]:
% 0.58/0.77         ( ( r2_hidden @ D @ C ) <=>
% 0.58/0.77           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.58/0.77  thf('19', plain,
% 0.58/0.77      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.58/0.77         (~ (r2_hidden @ X4 @ X3)
% 0.58/0.77          | (r2_hidden @ X4 @ X2)
% 0.58/0.77          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.58/0.77      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.58/0.77  thf('20', plain,
% 0.58/0.77      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.58/0.77         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.58/0.77      inference('simplify', [status(thm)], ['19'])).
% 0.58/0.77  thf('21', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.77         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.58/0.77          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['18', '20'])).
% 0.58/0.77  thf('22', plain,
% 0.58/0.77      (![X8 : $i, X9 : $i]:
% 0.58/0.77         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C @ X9 @ X8) @ X9))),
% 0.58/0.77      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.58/0.77  thf('23', plain,
% 0.58/0.77      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.58/0.77         (~ (r2_hidden @ X10 @ X8)
% 0.58/0.77          | ~ (r2_hidden @ X10 @ X11)
% 0.58/0.77          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.58/0.77      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.58/0.77  thf('24', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.77         ((r1_xboole_0 @ X1 @ X0)
% 0.58/0.77          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.58/0.77          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.58/0.77      inference('sup-', [status(thm)], ['22', '23'])).
% 0.58/0.77  thf('25', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.77         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.58/0.77          | ~ (r1_xboole_0 @ X2 @ X0)
% 0.58/0.77          | (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.58/0.77      inference('sup-', [status(thm)], ['21', '24'])).
% 0.58/0.77  thf('26', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.77         (~ (r1_xboole_0 @ X2 @ X0)
% 0.58/0.77          | (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.58/0.77      inference('simplify', [status(thm)], ['25'])).
% 0.58/0.77  thf('27', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.77         ((r2_hidden @ X0 @ X1)
% 0.58/0.77          | (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k1_tarski @ X0)) @ X1))),
% 0.58/0.77      inference('sup-', [status(thm)], ['17', '26'])).
% 0.58/0.77  thf(t7_xboole_0, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.78     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.58/0.78          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.58/0.78  thf('28', plain,
% 0.58/0.78      (![X12 : $i]:
% 0.58/0.78         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.58/0.78      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.58/0.78  thf('29', plain,
% 0.58/0.78      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.58/0.78         (~ (r2_hidden @ X4 @ X3)
% 0.58/0.78          | (r2_hidden @ X4 @ X1)
% 0.58/0.78          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.58/0.78      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.58/0.78  thf('30', plain,
% 0.58/0.78      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.58/0.78         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.58/0.78      inference('simplify', [status(thm)], ['29'])).
% 0.58/0.78  thf('31', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.58/0.78          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 0.58/0.78      inference('sup-', [status(thm)], ['28', '30'])).
% 0.58/0.78  thf('32', plain,
% 0.58/0.78      (![X12 : $i]:
% 0.58/0.78         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.58/0.78      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.58/0.78  thf('33', plain,
% 0.58/0.78      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.58/0.78         (~ (r2_hidden @ X10 @ X8)
% 0.58/0.78          | ~ (r2_hidden @ X10 @ X11)
% 0.58/0.78          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.58/0.78      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.58/0.78  thf('34', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         (((X0) = (k1_xboole_0))
% 0.58/0.78          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.58/0.78          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.58/0.78      inference('sup-', [status(thm)], ['32', '33'])).
% 0.58/0.78  thf('35', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0))
% 0.58/0.78          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.58/0.78          | ((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['31', '34'])).
% 0.58/0.78  thf('36', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         (~ (r1_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.58/0.78          | ((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)))),
% 0.58/0.78      inference('simplify', [status(thm)], ['35'])).
% 0.58/0.78  thf('37', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         ((r2_hidden @ X1 @ X0)
% 0.58/0.78          | ((k3_xboole_0 @ X0 @ (k1_tarski @ X1)) = (k1_xboole_0)))),
% 0.58/0.78      inference('sup-', [status(thm)], ['27', '36'])).
% 0.58/0.78  thf(t100_xboole_1, axiom,
% 0.58/0.78    (![A:$i,B:$i]:
% 0.58/0.78     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.58/0.78  thf('38', plain,
% 0.58/0.78      (![X13 : $i, X14 : $i]:
% 0.58/0.78         ((k4_xboole_0 @ X13 @ X14)
% 0.58/0.78           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.58/0.78      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.78  thf('39', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.58/0.78            = (k5_xboole_0 @ X1 @ k1_xboole_0))
% 0.58/0.78          | (r2_hidden @ X0 @ X1))),
% 0.58/0.78      inference('sup+', [status(thm)], ['37', '38'])).
% 0.58/0.78  thf('40', plain,
% 0.58/0.78      (![X12 : $i]:
% 0.58/0.78         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.58/0.78      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.58/0.78  thf('41', plain,
% 0.58/0.78      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.58/0.78         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.58/0.78      inference('simplify', [status(thm)], ['19'])).
% 0.58/0.78  thf('42', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.58/0.78          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.58/0.78      inference('sup-', [status(thm)], ['40', '41'])).
% 0.58/0.78  thf(t3_boole, axiom,
% 0.58/0.78    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.58/0.78  thf('43', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.58/0.78      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.78  thf('44', plain,
% 0.58/0.78      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 0.58/0.78      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.58/0.78  thf('45', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.58/0.78      inference('sup+', [status(thm)], ['43', '44'])).
% 0.58/0.78  thf('46', plain,
% 0.58/0.78      (![X24 : $i, X25 : $i]:
% 0.58/0.78         (~ (r1_xboole_0 @ (k1_tarski @ X24) @ X25) | ~ (r2_hidden @ X24 @ X25))),
% 0.58/0.78      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.58/0.78  thf('47', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.58/0.78      inference('sup-', [status(thm)], ['45', '46'])).
% 0.58/0.78  thf('48', plain,
% 0.58/0.78      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.58/0.78      inference('sup-', [status(thm)], ['42', '47'])).
% 0.58/0.78  thf('49', plain,
% 0.58/0.78      (![X13 : $i, X14 : $i]:
% 0.58/0.78         ((k4_xboole_0 @ X13 @ X14)
% 0.58/0.78           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.58/0.78      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.78  thf('50', plain,
% 0.58/0.78      (![X0 : $i]:
% 0.58/0.78         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.58/0.78      inference('sup+', [status(thm)], ['48', '49'])).
% 0.58/0.78  thf('51', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.58/0.78      inference('cnf', [status(esa)], [t3_boole])).
% 0.58/0.78  thf('52', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.58/0.78      inference('sup+', [status(thm)], ['50', '51'])).
% 0.58/0.78  thf('53', plain,
% 0.58/0.78      (![X0 : $i, X1 : $i]:
% 0.58/0.78         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 0.58/0.78          | (r2_hidden @ X0 @ X1))),
% 0.58/0.78      inference('demod', [status(thm)], ['39', '52'])).
% 0.58/0.78  thf('54', plain,
% 0.58/0.78      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) != (sk_A)))
% 0.58/0.78         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 0.58/0.78      inference('split', [status(esa)], ['3'])).
% 0.58/0.78  thf('55', plain,
% 0.58/0.78      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))) | 
% 0.58/0.78       ((r2_hidden @ sk_B_1 @ sk_A))),
% 0.58/0.78      inference('split', [status(esa)], ['3'])).
% 0.58/0.78  thf('56', plain,
% 0.58/0.78      (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 0.58/0.78      inference('sat_resolution*', [status(thm)], ['2', '12', '55'])).
% 0.58/0.78  thf('57', plain, (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) != (sk_A))),
% 0.58/0.78      inference('simpl_trail', [status(thm)], ['54', '56'])).
% 0.58/0.78  thf('58', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_B_1 @ sk_A))),
% 0.58/0.78      inference('sup-', [status(thm)], ['53', '57'])).
% 0.58/0.78  thf('59', plain, ((r2_hidden @ sk_B_1 @ sk_A)),
% 0.58/0.78      inference('simplify', [status(thm)], ['58'])).
% 0.58/0.78  thf('60', plain, ($false), inference('demod', [status(thm)], ['14', '59'])).
% 0.58/0.78  
% 0.58/0.78  % SZS output end Refutation
% 0.58/0.78  
% 0.58/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
