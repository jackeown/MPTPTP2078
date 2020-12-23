%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fCeyVaHTIo

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 (  85 expanded)
%              Number of leaves         :   28 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  640 ( 780 expanded)
%              Number of equality atoms :   52 (  65 expanded)
%              Maximal formula depth    :   19 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t32_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
      = ( k2_tarski @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
        = ( k2_tarski @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t32_relat_1])).

thf('0',plain,(
    ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ sk_A @ sk_B ) ) )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X9 @ X9 @ X10 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t23_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( C
          = ( k1_tarski @ ( k4_tarski @ A @ B ) ) )
       => ( ( ( k1_relat_1 @ C )
            = ( k1_tarski @ A ) )
          & ( ( k2_relat_1 @ C )
            = ( k1_tarski @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( X45
       != ( k1_tarski @ ( k4_tarski @ X43 @ X44 ) ) )
      | ( ( k1_relat_1 @ X45 )
        = ( k1_tarski @ X43 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t23_relat_1])).

thf('5',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X43 @ X44 ) ) )
      | ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X43 @ X44 ) ) )
        = ( k1_tarski @ X43 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(fc7_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ) )).

thf('7',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X39 @ X40 ) @ ( k4_tarski @ X41 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X43 @ X44 ) ) )
      = ( k1_tarski @ X43 ) ) ),
    inference(demod,[status(thm)],['5','8'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('10',plain,(
    ! [X38: $i] :
      ( ( ( k3_relat_1 @ X38 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X38 ) @ ( k2_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( X45
       != ( k1_tarski @ ( k4_tarski @ X43 @ X44 ) ) )
      | ( ( k2_relat_1 @ X45 )
        = ( k1_tarski @ X44 ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t23_relat_1])).

thf('13',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X43 @ X44 ) ) )
      | ( ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X43 @ X44 ) ) )
        = ( k1_tarski @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('15',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X43 @ X44 ) ) )
      = ( k1_tarski @ X44 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['11','15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['3','17'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X11 @ X11 @ X12 @ X13 )
      = ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k3_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k4_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22 )
      = ( k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('22',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k5_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k4_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( k6_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 ) @ ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t68_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('25',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( k6_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 )
      = ( k5_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) )
      = ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 ) ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k5_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k4_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) )
      = ( k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) )
      = ( k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4 ) ) ),
    inference('sup+',[status(thm)],['20','29'])).

thf('31',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( k4_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22 )
      = ( k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X4 ) )
      = ( k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference('sup+',[status(thm)],['19','32'])).

thf('34',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( k3_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17 )
      = ( k2_enumset1 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) )
      = ( k2_enumset1 @ X2 @ X1 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k2_enumset1 @ X11 @ X11 @ X12 @ X13 )
      = ( k1_enumset1 @ X11 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['18','35','36'])).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k1_enumset1 @ X9 @ X9 @ X10 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('39',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','37','38'])).

thf('40',plain,(
    $false ),
    inference(simplify,[status(thm)],['39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fCeyVaHTIo
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:31:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 99 iterations in 0.037s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.22/0.52                                           $i > $i).
% 0.22/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.52  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.22/0.52  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.22/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.52  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.22/0.52  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.22/0.52  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.22/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.52  thf(t32_relat_1, conjecture,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =
% 0.22/0.52       ( k2_tarski @ A @ B ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i]:
% 0.22/0.52        ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =
% 0.22/0.52          ( k2_tarski @ A @ B ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t32_relat_1])).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      (((k3_relat_1 @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))
% 0.22/0.52         != (k2_tarski @ sk_A @ sk_B))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t70_enumset1, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X9 : $i, X10 : $i]:
% 0.22/0.52         ((k1_enumset1 @ X9 @ X9 @ X10) = (k2_tarski @ X9 @ X10))),
% 0.22/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.52  thf(t69_enumset1, axiom,
% 0.22/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.52  thf('2', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 0.22/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.52  thf(t23_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ C ) =>
% 0.22/0.52       ( ( ( C ) = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =>
% 0.22/0.52         ( ( ( k1_relat_1 @ C ) = ( k1_tarski @ A ) ) & 
% 0.22/0.52           ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) ) ) ))).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.22/0.52         (((X45) != (k1_tarski @ (k4_tarski @ X43 @ X44)))
% 0.22/0.52          | ((k1_relat_1 @ X45) = (k1_tarski @ X43))
% 0.22/0.52          | ~ (v1_relat_1 @ X45))),
% 0.22/0.52      inference('cnf', [status(esa)], [t23_relat_1])).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (![X43 : $i, X44 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X43 @ X44)))
% 0.22/0.52          | ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X43 @ X44)))
% 0.22/0.52              = (k1_tarski @ X43)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['4'])).
% 0.22/0.52  thf('6', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 0.22/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.52  thf(fc7_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52     ( v1_relat_1 @
% 0.22/0.52       ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ))).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.22/0.52         (v1_relat_1 @ 
% 0.22/0.52          (k2_tarski @ (k4_tarski @ X39 @ X40) @ (k4_tarski @ X41 @ X42)))),
% 0.22/0.52      inference('cnf', [status(esa)], [fc7_relat_1])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      (![X43 : $i, X44 : $i]:
% 0.22/0.52         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X43 @ X44)))
% 0.22/0.52           = (k1_tarski @ X43))),
% 0.22/0.52      inference('demod', [status(thm)], ['5', '8'])).
% 0.22/0.52  thf(d6_relat_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ A ) =>
% 0.22/0.52       ( ( k3_relat_1 @ A ) =
% 0.22/0.52         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (![X38 : $i]:
% 0.22/0.52         (((k3_relat_1 @ X38)
% 0.22/0.52            = (k2_xboole_0 @ (k1_relat_1 @ X38) @ (k2_relat_1 @ X38)))
% 0.22/0.52          | ~ (v1_relat_1 @ X38))),
% 0.22/0.52      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((k3_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 0.22/0.52            = (k2_xboole_0 @ (k1_tarski @ X0) @ 
% 0.22/0.52               (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))
% 0.22/0.52          | ~ (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))),
% 0.22/0.52      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.22/0.52         (((X45) != (k1_tarski @ (k4_tarski @ X43 @ X44)))
% 0.22/0.52          | ((k2_relat_1 @ X45) = (k1_tarski @ X44))
% 0.22/0.52          | ~ (v1_relat_1 @ X45))),
% 0.22/0.52      inference('cnf', [status(esa)], [t23_relat_1])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X43 : $i, X44 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X43 @ X44)))
% 0.22/0.52          | ((k2_relat_1 @ (k1_tarski @ (k4_tarski @ X43 @ X44)))
% 0.22/0.52              = (k1_tarski @ X44)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['12'])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X43 : $i, X44 : $i]:
% 0.22/0.52         ((k2_relat_1 @ (k1_tarski @ (k4_tarski @ X43 @ X44)))
% 0.22/0.52           = (k1_tarski @ X44))),
% 0.22/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((k3_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 0.22/0.52           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.22/0.52      inference('demod', [status(thm)], ['11', '15', '16'])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((k3_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 0.22/0.52           = (k2_xboole_0 @ (k1_enumset1 @ X0 @ X0 @ X0) @ (k1_tarski @ X1)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['3', '17'])).
% 0.22/0.52  thf(t71_enumset1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.52         ((k2_enumset1 @ X11 @ X11 @ X12 @ X13)
% 0.22/0.52           = (k1_enumset1 @ X11 @ X12 @ X13))),
% 0.22/0.52      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.22/0.52  thf(t72_enumset1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.52         ((k3_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17)
% 0.22/0.52           = (k2_enumset1 @ X14 @ X15 @ X16 @ X17))),
% 0.22/0.52      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.22/0.52  thf(t73_enumset1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.52     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.22/0.52       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.52         ((k4_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22)
% 0.22/0.52           = (k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22))),
% 0.22/0.52      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.22/0.52  thf(t74_enumset1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.22/0.52     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.22/0.52       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.22/0.52         ((k5_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28)
% 0.22/0.52           = (k4_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28))),
% 0.22/0.52      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.22/0.52  thf(t68_enumset1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.22/0.52     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.22/0.52       ( k2_xboole_0 @
% 0.22/0.52         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ))).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.52         ((k6_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6 @ X7)
% 0.22/0.52           = (k2_xboole_0 @ (k5_enumset1 @ X0 @ X1 @ X2 @ X3 @ X4 @ X5 @ X6) @ 
% 0.22/0.52              (k1_tarski @ X7)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t68_enumset1])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.52         ((k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6)
% 0.22/0.52           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.22/0.52              (k1_tarski @ X6)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['22', '23'])).
% 0.22/0.52  thf(t75_enumset1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.22/0.52     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.22/0.52       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.22/0.52         ((k6_enumset1 @ X29 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35)
% 0.22/0.52           = (k5_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 @ X34 @ X35))),
% 0.22/0.52      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.52         ((k2_xboole_0 @ (k4_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.22/0.52           (k1_tarski @ X0)) = (k5_enumset1 @ X6 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['24', '25'])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.52         ((k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.22/0.52           (k1_tarski @ X5)) = (k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5))),
% 0.22/0.52      inference('sup+', [status(thm)], ['21', '26'])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.22/0.52         ((k5_enumset1 @ X23 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28)
% 0.22/0.52           = (k4_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28))),
% 0.22/0.52      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.52         ((k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.22/0.52           (k1_tarski @ X5)) = (k4_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5))),
% 0.22/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.52         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ (k1_tarski @ X4))
% 0.22/0.52           = (k4_enumset1 @ X3 @ X3 @ X2 @ X1 @ X0 @ X4))),
% 0.22/0.52      inference('sup+', [status(thm)], ['20', '29'])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.52         ((k4_enumset1 @ X18 @ X18 @ X19 @ X20 @ X21 @ X22)
% 0.22/0.52           = (k3_enumset1 @ X18 @ X19 @ X20 @ X21 @ X22))),
% 0.22/0.52      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.52         ((k2_xboole_0 @ (k2_enumset1 @ X3 @ X2 @ X1 @ X0) @ (k1_tarski @ X4))
% 0.22/0.52           = (k3_enumset1 @ X3 @ X2 @ X1 @ X0 @ X4))),
% 0.22/0.52      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.52         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 0.22/0.52           = (k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3))),
% 0.22/0.52      inference('sup+', [status(thm)], ['19', '32'])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.52         ((k3_enumset1 @ X14 @ X14 @ X15 @ X16 @ X17)
% 0.22/0.52           = (k2_enumset1 @ X14 @ X15 @ X16 @ X17))),
% 0.22/0.52      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.52         ((k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3))
% 0.22/0.52           = (k2_enumset1 @ X2 @ X1 @ X0 @ X3))),
% 0.22/0.52      inference('demod', [status(thm)], ['33', '34'])).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.52         ((k2_enumset1 @ X11 @ X11 @ X12 @ X13)
% 0.22/0.52           = (k1_enumset1 @ X11 @ X12 @ X13))),
% 0.22/0.52      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((k3_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 0.22/0.52           = (k1_enumset1 @ X0 @ X0 @ X1))),
% 0.22/0.52      inference('demod', [status(thm)], ['18', '35', '36'])).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      (![X9 : $i, X10 : $i]:
% 0.22/0.52         ((k1_enumset1 @ X9 @ X9 @ X10) = (k2_tarski @ X9 @ X10))),
% 0.22/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.52  thf('39', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['0', '37', '38'])).
% 0.22/0.52  thf('40', plain, ($false), inference('simplify', [status(thm)], ['39'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
