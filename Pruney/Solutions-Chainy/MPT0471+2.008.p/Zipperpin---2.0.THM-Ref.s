%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9EuD6F94lk

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:48 EST 2020

% Result     : Theorem 3.23s
% Output     : Refutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   80 (  95 expanded)
%              Number of leaves         :   26 (  39 expanded)
%              Depth                    :   17
%              Number of atoms          :  466 ( 592 expanded)
%              Number of equality atoms :   41 (  48 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X21: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X22 ) @ ( k1_relat_1 @ X22 ) )
      | ~ ( r2_hidden @ X23 @ ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t19_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 )
      = ( k4_xboole_0 @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_xboole_0 @ X12 @ X14 )
      | ( ( k4_xboole_0 @ X12 @ X14 )
       != X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','15'])).

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

thf('17',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X1 )
      | ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('25',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X1 )
      | ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 ) @ X0 )
      | ( ( k2_relat_1 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','29'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('31',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X21: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('36',plain,(
    ! [X20: $i] :
      ( ( ( k3_relat_1 @ X20 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X20 ) @ ( k2_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k3_relat_1 @ X0 )
        = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_relat_1 @ X0 )
        = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('41',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k3_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t63_relat_1,conjecture,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf(zf_stmt_0,negated_conjecture,(
    ( k3_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('cnf.neg',[status(esa)],[t63_relat_1])).

thf('45',plain,(
    ( k3_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k3_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','47'])).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9EuD6F94lk
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.23/3.42  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.23/3.42  % Solved by: fo/fo7.sh
% 3.23/3.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.23/3.42  % done 6958 iterations in 2.966s
% 3.23/3.42  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.23/3.42  % SZS output start Refutation
% 3.23/3.42  thf(sk_B_type, type, sk_B: $i > $i).
% 3.23/3.42  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.23/3.42  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.23/3.42  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.23/3.42  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.23/3.42  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.23/3.42  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 3.23/3.42  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.23/3.42  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.23/3.42  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.23/3.42  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.23/3.42  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 3.23/3.42  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.23/3.42  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.23/3.42  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.23/3.42      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.23/3.42  thf(fc10_relat_1, axiom,
% 3.23/3.42    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 3.23/3.42  thf('1', plain,
% 3.23/3.42      (![X21 : $i]:
% 3.23/3.42         ((v1_xboole_0 @ (k1_relat_1 @ X21)) | ~ (v1_xboole_0 @ X21))),
% 3.23/3.42      inference('cnf', [status(esa)], [fc10_relat_1])).
% 3.23/3.42  thf(t7_xboole_0, axiom,
% 3.23/3.42    (![A:$i]:
% 3.23/3.42     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 3.23/3.42          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 3.23/3.42  thf('2', plain,
% 3.23/3.42      (![X5 : $i]: (((X5) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X5) @ X5))),
% 3.23/3.42      inference('cnf', [status(esa)], [t7_xboole_0])).
% 3.23/3.42  thf(t19_relat_1, axiom,
% 3.23/3.42    (![A:$i,B:$i]:
% 3.23/3.42     ( ( v1_relat_1 @ B ) =>
% 3.23/3.42       ( ~( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) & 
% 3.23/3.42            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 3.23/3.42  thf('3', plain,
% 3.23/3.42      (![X22 : $i, X23 : $i]:
% 3.23/3.42         ((r2_hidden @ (sk_C_1 @ X22) @ (k1_relat_1 @ X22))
% 3.23/3.42          | ~ (r2_hidden @ X23 @ (k2_relat_1 @ X22))
% 3.23/3.42          | ~ (v1_relat_1 @ X22))),
% 3.23/3.42      inference('cnf', [status(esa)], [t19_relat_1])).
% 3.23/3.42  thf('4', plain,
% 3.23/3.42      (![X0 : $i]:
% 3.23/3.42         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 3.23/3.42          | ~ (v1_relat_1 @ X0)
% 3.23/3.42          | (r2_hidden @ (sk_C_1 @ X0) @ (k1_relat_1 @ X0)))),
% 3.23/3.42      inference('sup-', [status(thm)], ['2', '3'])).
% 3.23/3.42  thf(l13_xboole_0, axiom,
% 3.23/3.42    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.23/3.42  thf('5', plain,
% 3.23/3.42      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.23/3.42      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.23/3.42  thf(t1_boole, axiom,
% 3.23/3.42    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.23/3.42  thf('6', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 3.23/3.42      inference('cnf', [status(esa)], [t1_boole])).
% 3.23/3.42  thf(t46_xboole_1, axiom,
% 3.23/3.42    (![A:$i,B:$i]:
% 3.23/3.42     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 3.23/3.42  thf('7', plain,
% 3.23/3.42      (![X10 : $i, X11 : $i]:
% 3.23/3.42         ((k4_xboole_0 @ X10 @ (k2_xboole_0 @ X10 @ X11)) = (k1_xboole_0))),
% 3.23/3.42      inference('cnf', [status(esa)], [t46_xboole_1])).
% 3.23/3.42  thf('8', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.23/3.42      inference('sup+', [status(thm)], ['6', '7'])).
% 3.23/3.42  thf(t41_xboole_1, axiom,
% 3.23/3.42    (![A:$i,B:$i,C:$i]:
% 3.23/3.42     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 3.23/3.42       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.23/3.42  thf('9', plain,
% 3.23/3.42      (![X7 : $i, X8 : $i, X9 : $i]:
% 3.23/3.42         ((k4_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9)
% 3.23/3.42           = (k4_xboole_0 @ X7 @ (k2_xboole_0 @ X8 @ X9)))),
% 3.23/3.42      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.23/3.42  thf('10', plain,
% 3.23/3.42      (![X0 : $i, X1 : $i]:
% 3.23/3.42         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 3.23/3.42           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.23/3.42      inference('sup+', [status(thm)], ['8', '9'])).
% 3.23/3.42  thf('11', plain,
% 3.23/3.42      (![X10 : $i, X11 : $i]:
% 3.23/3.42         ((k4_xboole_0 @ X10 @ (k2_xboole_0 @ X10 @ X11)) = (k1_xboole_0))),
% 3.23/3.42      inference('cnf', [status(esa)], [t46_xboole_1])).
% 3.23/3.42  thf('12', plain,
% 3.23/3.42      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.23/3.42      inference('demod', [status(thm)], ['10', '11'])).
% 3.23/3.42  thf(t83_xboole_1, axiom,
% 3.23/3.42    (![A:$i,B:$i]:
% 3.23/3.42     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 3.23/3.42  thf('13', plain,
% 3.23/3.42      (![X12 : $i, X14 : $i]:
% 3.23/3.42         ((r1_xboole_0 @ X12 @ X14) | ((k4_xboole_0 @ X12 @ X14) != (X12)))),
% 3.23/3.42      inference('cnf', [status(esa)], [t83_xboole_1])).
% 3.23/3.42  thf('14', plain,
% 3.23/3.42      (![X0 : $i]:
% 3.23/3.42         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 3.23/3.42      inference('sup-', [status(thm)], ['12', '13'])).
% 3.23/3.42  thf('15', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 3.23/3.42      inference('simplify', [status(thm)], ['14'])).
% 3.23/3.42  thf('16', plain,
% 3.23/3.42      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.23/3.42      inference('sup+', [status(thm)], ['5', '15'])).
% 3.23/3.42  thf(t3_xboole_0, axiom,
% 3.23/3.42    (![A:$i,B:$i]:
% 3.23/3.42     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 3.23/3.42            ( r1_xboole_0 @ A @ B ) ) ) & 
% 3.23/3.42       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 3.23/3.42            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 3.23/3.42  thf('17', plain,
% 3.23/3.42      (![X1 : $i, X2 : $i]:
% 3.23/3.42         ((r1_xboole_0 @ X1 @ X2) | (r2_hidden @ (sk_C @ X2 @ X1) @ X1))),
% 3.23/3.42      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.23/3.42  thf('18', plain,
% 3.23/3.42      (![X1 : $i, X2 : $i]:
% 3.23/3.42         ((r1_xboole_0 @ X1 @ X2) | (r2_hidden @ (sk_C @ X2 @ X1) @ X2))),
% 3.23/3.42      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.23/3.42  thf('19', plain,
% 3.23/3.42      (![X1 : $i, X3 : $i, X4 : $i]:
% 3.23/3.42         (~ (r2_hidden @ X3 @ X1)
% 3.23/3.42          | ~ (r2_hidden @ X3 @ X4)
% 3.23/3.42          | ~ (r1_xboole_0 @ X1 @ X4))),
% 3.23/3.42      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.23/3.42  thf('20', plain,
% 3.23/3.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.23/3.42         ((r1_xboole_0 @ X1 @ X0)
% 3.23/3.42          | ~ (r1_xboole_0 @ X0 @ X2)
% 3.23/3.42          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 3.23/3.42      inference('sup-', [status(thm)], ['18', '19'])).
% 3.23/3.42  thf('21', plain,
% 3.23/3.42      (![X0 : $i, X1 : $i]:
% 3.23/3.42         ((r1_xboole_0 @ X0 @ X1)
% 3.23/3.42          | ~ (r1_xboole_0 @ X1 @ X0)
% 3.23/3.42          | (r1_xboole_0 @ X0 @ X1))),
% 3.23/3.42      inference('sup-', [status(thm)], ['17', '20'])).
% 3.23/3.42  thf('22', plain,
% 3.23/3.42      (![X0 : $i, X1 : $i]:
% 3.23/3.42         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 3.23/3.42      inference('simplify', [status(thm)], ['21'])).
% 3.23/3.42  thf('23', plain,
% 3.23/3.42      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X1) | (r1_xboole_0 @ X0 @ X1))),
% 3.23/3.42      inference('sup-', [status(thm)], ['16', '22'])).
% 3.23/3.42  thf('24', plain,
% 3.23/3.42      (![X0 : $i]:
% 3.23/3.42         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 3.23/3.42          | ~ (v1_relat_1 @ X0)
% 3.23/3.42          | (r2_hidden @ (sk_C_1 @ X0) @ (k1_relat_1 @ X0)))),
% 3.23/3.42      inference('sup-', [status(thm)], ['2', '3'])).
% 3.23/3.42  thf('25', plain,
% 3.23/3.42      (![X1 : $i, X3 : $i, X4 : $i]:
% 3.23/3.42         (~ (r2_hidden @ X3 @ X1)
% 3.23/3.42          | ~ (r2_hidden @ X3 @ X4)
% 3.23/3.42          | ~ (r1_xboole_0 @ X1 @ X4))),
% 3.23/3.42      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.23/3.42  thf('26', plain,
% 3.23/3.42      (![X0 : $i, X1 : $i]:
% 3.23/3.42         (~ (v1_relat_1 @ X0)
% 3.23/3.42          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 3.23/3.42          | ~ (r1_xboole_0 @ (k1_relat_1 @ X0) @ X1)
% 3.23/3.42          | ~ (r2_hidden @ (sk_C_1 @ X0) @ X1))),
% 3.23/3.42      inference('sup-', [status(thm)], ['24', '25'])).
% 3.23/3.42  thf('27', plain,
% 3.23/3.42      (![X0 : $i, X1 : $i]:
% 3.23/3.42         (~ (v1_xboole_0 @ X0)
% 3.23/3.42          | ~ (r2_hidden @ (sk_C_1 @ X1) @ X0)
% 3.23/3.42          | ((k2_relat_1 @ X1) = (k1_xboole_0))
% 3.23/3.42          | ~ (v1_relat_1 @ X1))),
% 3.23/3.42      inference('sup-', [status(thm)], ['23', '26'])).
% 3.23/3.42  thf('28', plain,
% 3.23/3.42      (![X0 : $i]:
% 3.23/3.42         (~ (v1_relat_1 @ X0)
% 3.23/3.42          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 3.23/3.42          | ~ (v1_relat_1 @ X0)
% 3.23/3.42          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 3.23/3.42          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 3.23/3.42      inference('sup-', [status(thm)], ['4', '27'])).
% 3.23/3.42  thf('29', plain,
% 3.23/3.42      (![X0 : $i]:
% 3.23/3.42         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 3.23/3.42          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 3.23/3.42          | ~ (v1_relat_1 @ X0))),
% 3.23/3.42      inference('simplify', [status(thm)], ['28'])).
% 3.23/3.42  thf('30', plain,
% 3.23/3.42      (![X0 : $i]:
% 3.23/3.42         (~ (v1_xboole_0 @ X0)
% 3.23/3.42          | ~ (v1_relat_1 @ X0)
% 3.23/3.42          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 3.23/3.42      inference('sup-', [status(thm)], ['1', '29'])).
% 3.23/3.42  thf(cc1_relat_1, axiom,
% 3.23/3.42    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 3.23/3.42  thf('31', plain, (![X19 : $i]: ((v1_relat_1 @ X19) | ~ (v1_xboole_0 @ X19))),
% 3.23/3.42      inference('cnf', [status(esa)], [cc1_relat_1])).
% 3.23/3.42  thf('32', plain,
% 3.23/3.42      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.23/3.42      inference('clc', [status(thm)], ['30', '31'])).
% 3.23/3.42  thf('33', plain,
% 3.23/3.42      (![X21 : $i]:
% 3.23/3.42         ((v1_xboole_0 @ (k1_relat_1 @ X21)) | ~ (v1_xboole_0 @ X21))),
% 3.23/3.42      inference('cnf', [status(esa)], [fc10_relat_1])).
% 3.23/3.42  thf('34', plain,
% 3.23/3.42      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.23/3.42      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.23/3.42  thf('35', plain,
% 3.23/3.42      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 3.23/3.42      inference('sup-', [status(thm)], ['33', '34'])).
% 3.23/3.42  thf(d6_relat_1, axiom,
% 3.23/3.42    (![A:$i]:
% 3.23/3.42     ( ( v1_relat_1 @ A ) =>
% 3.23/3.42       ( ( k3_relat_1 @ A ) =
% 3.23/3.42         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 3.23/3.42  thf('36', plain,
% 3.23/3.42      (![X20 : $i]:
% 3.23/3.42         (((k3_relat_1 @ X20)
% 3.23/3.42            = (k2_xboole_0 @ (k1_relat_1 @ X20) @ (k2_relat_1 @ X20)))
% 3.23/3.42          | ~ (v1_relat_1 @ X20))),
% 3.23/3.42      inference('cnf', [status(esa)], [d6_relat_1])).
% 3.23/3.42  thf('37', plain,
% 3.23/3.42      (![X0 : $i]:
% 3.23/3.42         (((k3_relat_1 @ X0) = (k2_xboole_0 @ k1_xboole_0 @ (k2_relat_1 @ X0)))
% 3.23/3.42          | ~ (v1_xboole_0 @ X0)
% 3.23/3.42          | ~ (v1_relat_1 @ X0))),
% 3.23/3.42      inference('sup+', [status(thm)], ['35', '36'])).
% 3.23/3.42  thf('38', plain, (![X19 : $i]: ((v1_relat_1 @ X19) | ~ (v1_xboole_0 @ X19))),
% 3.23/3.42      inference('cnf', [status(esa)], [cc1_relat_1])).
% 3.23/3.42  thf('39', plain,
% 3.23/3.42      (![X0 : $i]:
% 3.23/3.42         (~ (v1_xboole_0 @ X0)
% 3.23/3.42          | ((k3_relat_1 @ X0)
% 3.23/3.42              = (k2_xboole_0 @ k1_xboole_0 @ (k2_relat_1 @ X0))))),
% 3.23/3.42      inference('clc', [status(thm)], ['37', '38'])).
% 3.23/3.42  thf('40', plain,
% 3.23/3.42      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.23/3.42      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.23/3.42  thf('41', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 3.23/3.42      inference('cnf', [status(esa)], [t1_boole])).
% 3.23/3.42  thf('42', plain,
% 3.23/3.42      (![X0 : $i, X1 : $i]:
% 3.23/3.42         (((k2_xboole_0 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 3.23/3.42      inference('sup+', [status(thm)], ['40', '41'])).
% 3.23/3.42  thf('43', plain,
% 3.23/3.42      (![X0 : $i]:
% 3.23/3.42         (((k3_relat_1 @ X0) = (k1_xboole_0))
% 3.23/3.42          | ~ (v1_xboole_0 @ X0)
% 3.23/3.42          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 3.23/3.42      inference('sup+', [status(thm)], ['39', '42'])).
% 3.23/3.42  thf('44', plain,
% 3.23/3.42      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.23/3.42      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.23/3.42  thf(t63_relat_1, conjecture,
% 3.23/3.42    (( k3_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 3.23/3.42  thf(zf_stmt_0, negated_conjecture,
% 3.23/3.42    (( k3_relat_1 @ k1_xboole_0 ) != ( k1_xboole_0 )),
% 3.23/3.42    inference('cnf.neg', [status(esa)], [t63_relat_1])).
% 3.23/3.42  thf('45', plain, (((k3_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 3.23/3.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.23/3.42  thf('46', plain,
% 3.23/3.42      (![X0 : $i]:
% 3.23/3.42         (((k3_relat_1 @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.23/3.42      inference('sup-', [status(thm)], ['44', '45'])).
% 3.23/3.42  thf('47', plain,
% 3.23/3.42      (![X0 : $i]: (~ (v1_xboole_0 @ (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 3.23/3.42      inference('clc', [status(thm)], ['43', '46'])).
% 3.23/3.42  thf('48', plain,
% 3.23/3.42      (![X0 : $i]:
% 3.23/3.42         (~ (v1_xboole_0 @ k1_xboole_0)
% 3.23/3.42          | ~ (v1_xboole_0 @ X0)
% 3.23/3.42          | ~ (v1_xboole_0 @ X0))),
% 3.23/3.42      inference('sup-', [status(thm)], ['32', '47'])).
% 3.23/3.42  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.23/3.42      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.23/3.42  thf('50', plain, (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 3.23/3.42      inference('demod', [status(thm)], ['48', '49'])).
% 3.23/3.42  thf('51', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 3.23/3.42      inference('simplify', [status(thm)], ['50'])).
% 3.23/3.42  thf('52', plain, ($false), inference('sup-', [status(thm)], ['0', '51'])).
% 3.23/3.42  
% 3.23/3.42  % SZS output end Refutation
% 3.23/3.42  
% 3.23/3.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
