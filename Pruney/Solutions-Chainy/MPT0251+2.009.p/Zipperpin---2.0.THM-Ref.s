%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HRMe0BbC1y

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:02 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 122 expanded)
%              Number of leaves         :   25 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  513 ( 774 expanded)
%              Number of equality atoms :   53 (  87 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t46_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t46_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X51: $i,X53: $i,X54: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X51 @ X53 ) @ X54 )
      | ~ ( r2_hidden @ X53 @ X54 )
      | ~ ( r2_hidden @ X51 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X39: $i] :
      ( ( k2_tarski @ X39 @ X39 )
      = ( k1_tarski @ X39 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('6',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(demod,[status(thm)],['4','5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_xboole_0 @ X31 @ X32 )
        = X31 )
      | ~ ( r1_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( r2_hidden @ X15 @ X13 )
      | ( X14
       != ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('11',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X10 )
      | ~ ( r2_hidden @ ( sk_C @ X10 @ X8 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_xboole_0 @ X31 @ X32 )
        = X31 )
      | ~ ( r1_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ X29 )
      = ( k5_xboole_0 @ X28 @ ( k3_xboole_0 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X2 )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X30: $i] :
      ( ( k2_xboole_0 @ X30 @ k1_xboole_0 )
      = X30 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X35 @ X36 ) @ X36 )
      = ( k4_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ X26 )
      | ( X25 != X26 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X26: $i] :
      ( r1_tarski @ X26 @ X26 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_xboole_0 @ X31 @ X32 )
        = X31 )
      | ~ ( r1_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ X29 )
      = ( k5_xboole_0 @ X28 @ ( k3_xboole_0 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','30'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k2_xboole_0 @ X33 @ ( k4_xboole_0 @ X34 @ X33 ) )
      = ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('38',plain,(
    ! [X37: $i,X38: $i] :
      ( r1_tarski @ X37 @ ( k2_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_xboole_0 @ X31 @ X32 )
        = X31 )
      | ~ ( r1_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ X29 )
      = ( k5_xboole_0 @ X28 @ ( k3_xboole_0 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X1 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','47'])).

thf('49',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k2_xboole_0 @ X33 @ ( k4_xboole_0 @ X34 @ X33 ) )
      = ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X30: $i] :
      ( ( k2_xboole_0 @ X30 @ k1_xboole_0 )
      = X30 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','52'])).

thf('54',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X3 @ X2 )
      = ( k2_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('56',plain,(
    ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
 != sk_B_1 ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['53','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HRMe0BbC1y
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:56:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.44/1.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.44/1.68  % Solved by: fo/fo7.sh
% 1.44/1.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.44/1.68  % done 3979 iterations in 1.193s
% 1.44/1.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.44/1.68  % SZS output start Refutation
% 1.44/1.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.44/1.68  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.44/1.68  thf(sk_A_type, type, sk_A: $i).
% 1.44/1.68  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.44/1.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.44/1.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.44/1.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.44/1.68  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.44/1.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.44/1.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.44/1.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.44/1.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.44/1.68  thf(t46_zfmisc_1, conjecture,
% 1.44/1.68    (![A:$i,B:$i]:
% 1.44/1.68     ( ( r2_hidden @ A @ B ) =>
% 1.44/1.68       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 1.44/1.68  thf(zf_stmt_0, negated_conjecture,
% 1.44/1.68    (~( ![A:$i,B:$i]:
% 1.44/1.68        ( ( r2_hidden @ A @ B ) =>
% 1.44/1.68          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 1.44/1.68    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 1.44/1.68  thf('0', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 1.44/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.68  thf('1', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 1.44/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.68  thf(t38_zfmisc_1, axiom,
% 1.44/1.68    (![A:$i,B:$i,C:$i]:
% 1.44/1.68     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 1.44/1.68       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 1.44/1.68  thf('2', plain,
% 1.44/1.68      (![X51 : $i, X53 : $i, X54 : $i]:
% 1.44/1.68         ((r1_tarski @ (k2_tarski @ X51 @ X53) @ X54)
% 1.44/1.68          | ~ (r2_hidden @ X53 @ X54)
% 1.44/1.68          | ~ (r2_hidden @ X51 @ X54))),
% 1.44/1.68      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 1.44/1.68  thf('3', plain,
% 1.44/1.68      (![X0 : $i]:
% 1.44/1.68         (~ (r2_hidden @ X0 @ sk_B_1)
% 1.44/1.68          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B_1))),
% 1.44/1.68      inference('sup-', [status(thm)], ['1', '2'])).
% 1.44/1.68  thf('4', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ sk_B_1)),
% 1.44/1.68      inference('sup-', [status(thm)], ['0', '3'])).
% 1.44/1.68  thf(t69_enumset1, axiom,
% 1.44/1.68    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.44/1.68  thf('5', plain, (![X39 : $i]: ((k2_tarski @ X39 @ X39) = (k1_tarski @ X39))),
% 1.44/1.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.44/1.68  thf('6', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 1.44/1.68      inference('demod', [status(thm)], ['4', '5'])).
% 1.44/1.68  thf(t28_xboole_1, axiom,
% 1.44/1.68    (![A:$i,B:$i]:
% 1.44/1.68     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.44/1.68  thf('7', plain,
% 1.44/1.68      (![X31 : $i, X32 : $i]:
% 1.44/1.68         (((k3_xboole_0 @ X31 @ X32) = (X31)) | ~ (r1_tarski @ X31 @ X32))),
% 1.44/1.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.44/1.68  thf('8', plain,
% 1.44/1.68      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))),
% 1.44/1.68      inference('sup-', [status(thm)], ['6', '7'])).
% 1.44/1.68  thf(d3_tarski, axiom,
% 1.44/1.68    (![A:$i,B:$i]:
% 1.44/1.68     ( ( r1_tarski @ A @ B ) <=>
% 1.44/1.68       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.44/1.68  thf('9', plain,
% 1.44/1.68      (![X8 : $i, X10 : $i]:
% 1.44/1.68         ((r1_tarski @ X8 @ X10) | (r2_hidden @ (sk_C @ X10 @ X8) @ X8))),
% 1.44/1.68      inference('cnf', [status(esa)], [d3_tarski])).
% 1.44/1.68  thf(d4_xboole_0, axiom,
% 1.44/1.68    (![A:$i,B:$i,C:$i]:
% 1.44/1.68     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.44/1.68       ( ![D:$i]:
% 1.44/1.68         ( ( r2_hidden @ D @ C ) <=>
% 1.44/1.68           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.44/1.68  thf('10', plain,
% 1.44/1.68      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 1.44/1.68         (~ (r2_hidden @ X15 @ X14)
% 1.44/1.68          | (r2_hidden @ X15 @ X13)
% 1.44/1.68          | ((X14) != (k3_xboole_0 @ X12 @ X13)))),
% 1.44/1.68      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.44/1.68  thf('11', plain,
% 1.44/1.68      (![X12 : $i, X13 : $i, X15 : $i]:
% 1.44/1.68         ((r2_hidden @ X15 @ X13)
% 1.44/1.68          | ~ (r2_hidden @ X15 @ (k3_xboole_0 @ X12 @ X13)))),
% 1.44/1.68      inference('simplify', [status(thm)], ['10'])).
% 1.44/1.68  thf('12', plain,
% 1.44/1.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.44/1.68         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.44/1.68          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 1.44/1.68      inference('sup-', [status(thm)], ['9', '11'])).
% 1.44/1.68  thf('13', plain,
% 1.44/1.68      (![X8 : $i, X10 : $i]:
% 1.44/1.68         ((r1_tarski @ X8 @ X10) | ~ (r2_hidden @ (sk_C @ X10 @ X8) @ X10))),
% 1.44/1.68      inference('cnf', [status(esa)], [d3_tarski])).
% 1.44/1.68  thf('14', plain,
% 1.44/1.68      (![X0 : $i, X1 : $i]:
% 1.44/1.68         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 1.44/1.68          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 1.44/1.68      inference('sup-', [status(thm)], ['12', '13'])).
% 1.44/1.68  thf('15', plain,
% 1.44/1.68      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.44/1.68      inference('simplify', [status(thm)], ['14'])).
% 1.44/1.68  thf('16', plain,
% 1.44/1.68      (![X31 : $i, X32 : $i]:
% 1.44/1.68         (((k3_xboole_0 @ X31 @ X32) = (X31)) | ~ (r1_tarski @ X31 @ X32))),
% 1.44/1.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.44/1.68  thf('17', plain,
% 1.44/1.68      (![X0 : $i, X1 : $i]:
% 1.44/1.68         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 1.44/1.68           = (k3_xboole_0 @ X1 @ X0))),
% 1.44/1.68      inference('sup-', [status(thm)], ['15', '16'])).
% 1.44/1.68  thf(t100_xboole_1, axiom,
% 1.44/1.68    (![A:$i,B:$i]:
% 1.44/1.68     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.44/1.68  thf('18', plain,
% 1.44/1.68      (![X28 : $i, X29 : $i]:
% 1.44/1.68         ((k4_xboole_0 @ X28 @ X29)
% 1.44/1.68           = (k5_xboole_0 @ X28 @ (k3_xboole_0 @ X28 @ X29)))),
% 1.44/1.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.44/1.68  thf('19', plain,
% 1.44/1.68      (![X0 : $i, X1 : $i]:
% 1.44/1.68         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 1.44/1.68           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.44/1.68      inference('sup+', [status(thm)], ['17', '18'])).
% 1.44/1.68  thf(commutativity_k2_xboole_0, axiom,
% 1.44/1.68    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.44/1.68  thf('20', plain,
% 1.44/1.68      (![X2 : $i, X3 : $i]: ((k2_xboole_0 @ X3 @ X2) = (k2_xboole_0 @ X2 @ X3))),
% 1.44/1.68      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.44/1.68  thf(t1_boole, axiom,
% 1.44/1.68    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.44/1.68  thf('21', plain, (![X30 : $i]: ((k2_xboole_0 @ X30 @ k1_xboole_0) = (X30))),
% 1.44/1.68      inference('cnf', [status(esa)], [t1_boole])).
% 1.44/1.68  thf('22', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.44/1.68      inference('sup+', [status(thm)], ['20', '21'])).
% 1.44/1.68  thf(t40_xboole_1, axiom,
% 1.44/1.68    (![A:$i,B:$i]:
% 1.44/1.68     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.44/1.68  thf('23', plain,
% 1.44/1.68      (![X35 : $i, X36 : $i]:
% 1.44/1.68         ((k4_xboole_0 @ (k2_xboole_0 @ X35 @ X36) @ X36)
% 1.44/1.68           = (k4_xboole_0 @ X35 @ X36))),
% 1.44/1.68      inference('cnf', [status(esa)], [t40_xboole_1])).
% 1.44/1.68  thf('24', plain,
% 1.44/1.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.44/1.68      inference('sup+', [status(thm)], ['22', '23'])).
% 1.44/1.68  thf(d10_xboole_0, axiom,
% 1.44/1.68    (![A:$i,B:$i]:
% 1.44/1.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.44/1.68  thf('25', plain,
% 1.44/1.68      (![X25 : $i, X26 : $i]: ((r1_tarski @ X25 @ X26) | ((X25) != (X26)))),
% 1.44/1.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.44/1.68  thf('26', plain, (![X26 : $i]: (r1_tarski @ X26 @ X26)),
% 1.44/1.68      inference('simplify', [status(thm)], ['25'])).
% 1.44/1.68  thf('27', plain,
% 1.44/1.68      (![X31 : $i, X32 : $i]:
% 1.44/1.68         (((k3_xboole_0 @ X31 @ X32) = (X31)) | ~ (r1_tarski @ X31 @ X32))),
% 1.44/1.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.44/1.68  thf('28', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.44/1.68      inference('sup-', [status(thm)], ['26', '27'])).
% 1.44/1.68  thf('29', plain,
% 1.44/1.68      (![X28 : $i, X29 : $i]:
% 1.44/1.68         ((k4_xboole_0 @ X28 @ X29)
% 1.44/1.68           = (k5_xboole_0 @ X28 @ (k3_xboole_0 @ X28 @ X29)))),
% 1.44/1.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.44/1.68  thf('30', plain,
% 1.44/1.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.44/1.68      inference('sup+', [status(thm)], ['28', '29'])).
% 1.44/1.68  thf('31', plain,
% 1.44/1.68      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.44/1.68      inference('demod', [status(thm)], ['24', '30'])).
% 1.44/1.68  thf(t39_xboole_1, axiom,
% 1.44/1.68    (![A:$i,B:$i]:
% 1.44/1.68     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.44/1.68  thf('32', plain,
% 1.44/1.68      (![X33 : $i, X34 : $i]:
% 1.44/1.68         ((k2_xboole_0 @ X33 @ (k4_xboole_0 @ X34 @ X33))
% 1.44/1.68           = (k2_xboole_0 @ X33 @ X34))),
% 1.44/1.68      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.44/1.68  thf('33', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.44/1.68      inference('sup+', [status(thm)], ['20', '21'])).
% 1.44/1.68  thf('34', plain,
% 1.44/1.68      (![X0 : $i]:
% 1.44/1.68         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.44/1.68      inference('sup+', [status(thm)], ['32', '33'])).
% 1.44/1.68  thf('35', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.44/1.68      inference('sup+', [status(thm)], ['20', '21'])).
% 1.44/1.68  thf('36', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.44/1.68      inference('sup+', [status(thm)], ['34', '35'])).
% 1.44/1.68  thf('37', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.44/1.68      inference('sup+', [status(thm)], ['20', '21'])).
% 1.44/1.68  thf(t7_xboole_1, axiom,
% 1.44/1.68    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.44/1.68  thf('38', plain,
% 1.44/1.68      (![X37 : $i, X38 : $i]: (r1_tarski @ X37 @ (k2_xboole_0 @ X37 @ X38))),
% 1.44/1.68      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.44/1.68  thf('39', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.44/1.68      inference('sup+', [status(thm)], ['37', '38'])).
% 1.44/1.68  thf('40', plain,
% 1.44/1.68      (![X31 : $i, X32 : $i]:
% 1.44/1.68         (((k3_xboole_0 @ X31 @ X32) = (X31)) | ~ (r1_tarski @ X31 @ X32))),
% 1.44/1.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.44/1.68  thf('41', plain,
% 1.44/1.68      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.44/1.68      inference('sup-', [status(thm)], ['39', '40'])).
% 1.44/1.68  thf('42', plain,
% 1.44/1.68      (![X28 : $i, X29 : $i]:
% 1.44/1.68         ((k4_xboole_0 @ X28 @ X29)
% 1.44/1.68           = (k5_xboole_0 @ X28 @ (k3_xboole_0 @ X28 @ X29)))),
% 1.44/1.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.44/1.68  thf('43', plain,
% 1.44/1.68      (![X0 : $i]:
% 1.44/1.68         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 1.44/1.68           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 1.44/1.68      inference('sup+', [status(thm)], ['41', '42'])).
% 1.44/1.68  thf('44', plain,
% 1.44/1.68      (![X0 : $i]:
% 1.44/1.68         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 1.44/1.68           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 1.44/1.68      inference('sup+', [status(thm)], ['41', '42'])).
% 1.44/1.68  thf('45', plain,
% 1.44/1.68      (![X0 : $i, X1 : $i]:
% 1.44/1.68         ((k4_xboole_0 @ k1_xboole_0 @ X1) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 1.44/1.68      inference('sup+', [status(thm)], ['43', '44'])).
% 1.44/1.68  thf('46', plain,
% 1.44/1.68      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.44/1.68      inference('sup+', [status(thm)], ['36', '45'])).
% 1.44/1.68  thf('47', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.44/1.68      inference('demod', [status(thm)], ['31', '46'])).
% 1.44/1.68  thf('48', plain,
% 1.44/1.68      (![X0 : $i, X1 : $i]:
% 1.44/1.68         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 1.44/1.68      inference('demod', [status(thm)], ['19', '47'])).
% 1.44/1.68  thf('49', plain,
% 1.44/1.68      (![X33 : $i, X34 : $i]:
% 1.44/1.68         ((k2_xboole_0 @ X33 @ (k4_xboole_0 @ X34 @ X33))
% 1.44/1.68           = (k2_xboole_0 @ X33 @ X34))),
% 1.44/1.68      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.44/1.68  thf('50', plain,
% 1.44/1.68      (![X0 : $i, X1 : $i]:
% 1.44/1.68         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 1.44/1.68           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.44/1.68      inference('sup+', [status(thm)], ['48', '49'])).
% 1.44/1.68  thf('51', plain, (![X30 : $i]: ((k2_xboole_0 @ X30 @ k1_xboole_0) = (X30))),
% 1.44/1.68      inference('cnf', [status(esa)], [t1_boole])).
% 1.44/1.68  thf('52', plain,
% 1.44/1.68      (![X0 : $i, X1 : $i]:
% 1.44/1.68         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.44/1.68      inference('demod', [status(thm)], ['50', '51'])).
% 1.44/1.68  thf('53', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 1.44/1.68      inference('sup+', [status(thm)], ['8', '52'])).
% 1.44/1.68  thf('54', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (sk_B_1))),
% 1.44/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.44/1.68  thf('55', plain,
% 1.44/1.68      (![X2 : $i, X3 : $i]: ((k2_xboole_0 @ X3 @ X2) = (k2_xboole_0 @ X2 @ X3))),
% 1.44/1.68      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.44/1.68  thf('56', plain, (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) != (sk_B_1))),
% 1.44/1.68      inference('demod', [status(thm)], ['54', '55'])).
% 1.44/1.68  thf('57', plain, ($false),
% 1.44/1.68      inference('simplify_reflect-', [status(thm)], ['53', '56'])).
% 1.44/1.68  
% 1.44/1.68  % SZS output end Refutation
% 1.44/1.68  
% 1.44/1.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
