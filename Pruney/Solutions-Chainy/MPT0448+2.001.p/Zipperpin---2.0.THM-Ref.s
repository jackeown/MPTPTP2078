%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.igDHUvu3By

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:00 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   62 (  76 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :  514 ( 646 expanded)
%              Number of equality atoms :   50 (  65 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t24_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( v1_relat_1 @ E )
     => ( ( E
          = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) )
       => ( ( ( k1_relat_1 @ E )
            = ( k2_tarski @ A @ C ) )
          & ( ( k2_relat_1 @ E )
            = ( k2_tarski @ B @ D ) ) ) ) ) )).

thf('2',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( X39
       != ( k2_tarski @ ( k4_tarski @ X35 @ X36 ) @ ( k4_tarski @ X37 @ X38 ) ) )
      | ( ( k1_relat_1 @ X39 )
        = ( k2_tarski @ X35 @ X37 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t24_relat_1])).

thf('3',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X35 @ X36 ) @ ( k4_tarski @ X37 @ X38 ) ) )
      | ( ( k1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X35 @ X36 ) @ ( k4_tarski @ X37 @ X38 ) ) )
        = ( k2_tarski @ X35 @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X1 @ X0 ) @ ( k4_tarski @ X1 @ X0 ) ) )
        = ( k2_tarski @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(fc5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X33: $i,X34: $i] :
      ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_relat_1])).

thf(t36_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) )
      & ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        = ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X22 ) @ ( k2_tarski @ X23 @ X24 ) )
      = ( k2_tarski @ ( k4_tarski @ X22 @ X23 ) @ ( k4_tarski @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) )
      = ( k2_tarski @ X1 @ X1 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
      = ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X20 ) @ ( k1_tarski @ X21 ) )
      = ( k1_tarski @ ( k4_tarski @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t35_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k2_tarski @ X1 @ X1 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X32: $i] :
      ( ( ( k3_relat_1 @ X32 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
        = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('15',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( X39
       != ( k2_tarski @ ( k4_tarski @ X35 @ X36 ) @ ( k4_tarski @ X37 @ X38 ) ) )
      | ( ( k2_relat_1 @ X39 )
        = ( k2_tarski @ X36 @ X38 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t24_relat_1])).

thf('16',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_relat_1 @ ( k2_tarski @ ( k4_tarski @ X35 @ X36 ) @ ( k4_tarski @ X37 @ X38 ) ) )
      | ( ( k2_relat_1 @ ( k2_tarski @ ( k4_tarski @ X35 @ X36 ) @ ( k4_tarski @ X37 @ X38 ) ) )
        = ( k2_tarski @ X36 @ X38 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k2_tarski @ ( k4_tarski @ X1 @ X0 ) @ ( k4_tarski @ X1 @ X0 ) ) )
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X33: $i,X34: $i] :
      ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_relat_1])).

thf('19',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X22 ) @ ( k2_tarski @ X23 @ X24 ) )
      = ( k2_tarski @ ( k4_tarski @ X22 @ X23 ) @ ( k4_tarski @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t36_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relat_1 @ ( k1_tarski @ ( k4_tarski @ X1 @ X0 ) ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X15: $i] :
      ( ( k2_tarski @ X15 @ X15 )
      = ( k1_tarski @ X15 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t93_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X30 @ X31 ) )
      = ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t93_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X30 @ X31 ) )
      = ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t93_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_tarski @ X13 @ X14 )
      = ( k2_xboole_0 @ ( k1_tarski @ X13 ) @ ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X33: $i,X34: $i] :
      ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_relat_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ X0 @ X1 ) ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','24','33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('37',plain,(
    ( k2_tarski @ sk_A @ sk_B )
 != ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','35','36'])).

thf('38',plain,(
    $false ),
    inference(simplify,[status(thm)],['37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.igDHUvu3By
% 0.16/0.38  % Computer   : n002.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 18:09:07 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.39  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.45/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.67  % Solved by: fo/fo7.sh
% 0.45/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.67  % done 408 iterations in 0.174s
% 0.45/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.67  % SZS output start Refutation
% 0.45/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.67  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.67  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.45/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.67  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.67  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.45/0.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.67  thf(t32_relat_1, conjecture,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =
% 0.45/0.67       ( k2_tarski @ A @ B ) ))).
% 0.45/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.67    (~( ![A:$i,B:$i]:
% 0.45/0.67        ( ( k3_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) ) =
% 0.45/0.67          ( k2_tarski @ A @ B ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t32_relat_1])).
% 0.45/0.67  thf('0', plain,
% 0.45/0.67      (((k3_relat_1 @ (k1_tarski @ (k4_tarski @ sk_A @ sk_B)))
% 0.45/0.67         != (k2_tarski @ sk_A @ sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(t69_enumset1, axiom,
% 0.45/0.67    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.67  thf('1', plain, (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.45/0.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.67  thf(t24_relat_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.45/0.67     ( ( v1_relat_1 @ E ) =>
% 0.45/0.67       ( ( ( E ) =
% 0.45/0.67           ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ C @ D ) ) ) =>
% 0.45/0.67         ( ( ( k1_relat_1 @ E ) = ( k2_tarski @ A @ C ) ) & 
% 0.45/0.67           ( ( k2_relat_1 @ E ) = ( k2_tarski @ B @ D ) ) ) ) ))).
% 0.45/0.67  thf('2', plain,
% 0.45/0.67      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.45/0.67         (((X39)
% 0.45/0.67            != (k2_tarski @ (k4_tarski @ X35 @ X36) @ (k4_tarski @ X37 @ X38)))
% 0.45/0.67          | ((k1_relat_1 @ X39) = (k2_tarski @ X35 @ X37))
% 0.45/0.67          | ~ (v1_relat_1 @ X39))),
% 0.45/0.67      inference('cnf', [status(esa)], [t24_relat_1])).
% 0.45/0.67  thf('3', plain,
% 0.45/0.67      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.45/0.67         (~ (v1_relat_1 @ 
% 0.45/0.67             (k2_tarski @ (k4_tarski @ X35 @ X36) @ (k4_tarski @ X37 @ X38)))
% 0.45/0.67          | ((k1_relat_1 @ 
% 0.45/0.67              (k2_tarski @ (k4_tarski @ X35 @ X36) @ (k4_tarski @ X37 @ X38)))
% 0.45/0.67              = (k2_tarski @ X35 @ X37)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['2'])).
% 0.45/0.67  thf('4', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (~ (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.45/0.67          | ((k1_relat_1 @ 
% 0.45/0.67              (k2_tarski @ (k4_tarski @ X1 @ X0) @ (k4_tarski @ X1 @ X0)))
% 0.45/0.67              = (k2_tarski @ X1 @ X1)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['1', '3'])).
% 0.45/0.67  thf(fc5_relat_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( v1_relat_1 @ ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 0.45/0.67  thf('5', plain,
% 0.45/0.67      (![X33 : $i, X34 : $i]:
% 0.45/0.67         (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X33 @ X34)))),
% 0.45/0.67      inference('cnf', [status(esa)], [fc5_relat_1])).
% 0.45/0.67  thf(t36_zfmisc_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( ( k2_zfmisc_1 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =
% 0.45/0.67         ( k2_tarski @ ( k4_tarski @ A @ C ) @ ( k4_tarski @ B @ C ) ) ) & 
% 0.45/0.67       ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) =
% 0.45/0.67         ( k2_tarski @ ( k4_tarski @ A @ B ) @ ( k4_tarski @ A @ C ) ) ) ))).
% 0.45/0.67  thf('6', plain,
% 0.45/0.67      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.67         ((k2_zfmisc_1 @ (k1_tarski @ X22) @ (k2_tarski @ X23 @ X24))
% 0.45/0.67           = (k2_tarski @ (k4_tarski @ X22 @ X23) @ (k4_tarski @ X22 @ X24)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.45/0.67  thf('7', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k1_relat_1 @ 
% 0.45/0.67           (k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0)))
% 0.45/0.67           = (k2_tarski @ X1 @ X1))),
% 0.45/0.67      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.45/0.67  thf('8', plain, (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.45/0.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.67  thf(t35_zfmisc_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.45/0.67       ( k1_tarski @ ( k4_tarski @ A @ B ) ) ))).
% 0.45/0.67  thf('9', plain,
% 0.45/0.67      (![X20 : $i, X21 : $i]:
% 0.45/0.67         ((k2_zfmisc_1 @ (k1_tarski @ X20) @ (k1_tarski @ X21))
% 0.45/0.67           = (k1_tarski @ (k4_tarski @ X20 @ X21)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t35_zfmisc_1])).
% 0.45/0.67  thf('10', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 0.45/0.67           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['8', '9'])).
% 0.45/0.67  thf('11', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.45/0.67           = (k2_tarski @ X1 @ X1))),
% 0.45/0.67      inference('demod', [status(thm)], ['7', '10'])).
% 0.45/0.67  thf(d6_relat_1, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( v1_relat_1 @ A ) =>
% 0.45/0.67       ( ( k3_relat_1 @ A ) =
% 0.45/0.67         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.45/0.67  thf('12', plain,
% 0.45/0.67      (![X32 : $i]:
% 0.45/0.67         (((k3_relat_1 @ X32)
% 0.45/0.67            = (k2_xboole_0 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32)))
% 0.45/0.67          | ~ (v1_relat_1 @ X32))),
% 0.45/0.67      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.45/0.67  thf('13', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (((k3_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 0.45/0.67            = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ 
% 0.45/0.67               (k2_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))))
% 0.45/0.67          | ~ (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1))))),
% 0.45/0.67      inference('sup+', [status(thm)], ['11', '12'])).
% 0.45/0.67  thf('14', plain,
% 0.45/0.67      (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.45/0.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.67  thf('15', plain,
% 0.45/0.67      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.45/0.67         (((X39)
% 0.45/0.67            != (k2_tarski @ (k4_tarski @ X35 @ X36) @ (k4_tarski @ X37 @ X38)))
% 0.45/0.67          | ((k2_relat_1 @ X39) = (k2_tarski @ X36 @ X38))
% 0.45/0.67          | ~ (v1_relat_1 @ X39))),
% 0.45/0.67      inference('cnf', [status(esa)], [t24_relat_1])).
% 0.45/0.67  thf('16', plain,
% 0.45/0.67      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.45/0.67         (~ (v1_relat_1 @ 
% 0.45/0.67             (k2_tarski @ (k4_tarski @ X35 @ X36) @ (k4_tarski @ X37 @ X38)))
% 0.45/0.67          | ((k2_relat_1 @ 
% 0.45/0.67              (k2_tarski @ (k4_tarski @ X35 @ X36) @ (k4_tarski @ X37 @ X38)))
% 0.45/0.67              = (k2_tarski @ X36 @ X38)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['15'])).
% 0.45/0.67  thf('17', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (~ (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.45/0.67          | ((k2_relat_1 @ 
% 0.45/0.67              (k2_tarski @ (k4_tarski @ X1 @ X0) @ (k4_tarski @ X1 @ X0)))
% 0.45/0.67              = (k2_tarski @ X0 @ X0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['14', '16'])).
% 0.45/0.67  thf('18', plain,
% 0.45/0.67      (![X33 : $i, X34 : $i]:
% 0.45/0.67         (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X33 @ X34)))),
% 0.45/0.67      inference('cnf', [status(esa)], [fc5_relat_1])).
% 0.45/0.67  thf('19', plain,
% 0.45/0.67      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.67         ((k2_zfmisc_1 @ (k1_tarski @ X22) @ (k2_tarski @ X23 @ X24))
% 0.45/0.67           = (k2_tarski @ (k4_tarski @ X22 @ X23) @ (k4_tarski @ X22 @ X24)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t36_zfmisc_1])).
% 0.45/0.67  thf('20', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k2_relat_1 @ 
% 0.45/0.67           (k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0)))
% 0.45/0.67           = (k2_tarski @ X0 @ X0))),
% 0.45/0.67      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.45/0.67  thf('21', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k2_zfmisc_1 @ (k1_tarski @ X1) @ (k2_tarski @ X0 @ X0))
% 0.45/0.67           = (k1_tarski @ (k4_tarski @ X1 @ X0)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['8', '9'])).
% 0.45/0.67  thf('22', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0)))
% 0.45/0.67           = (k2_tarski @ X0 @ X0))),
% 0.45/0.67      inference('demod', [status(thm)], ['20', '21'])).
% 0.45/0.67  thf('23', plain,
% 0.45/0.67      (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.45/0.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.67  thf('24', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k2_relat_1 @ (k1_tarski @ (k4_tarski @ X1 @ X0))) = (k1_tarski @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['22', '23'])).
% 0.45/0.67  thf('25', plain,
% 0.45/0.67      (![X15 : $i]: ((k2_tarski @ X15 @ X15) = (k1_tarski @ X15))),
% 0.45/0.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.67  thf(commutativity_k2_tarski, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.45/0.67  thf('26', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.45/0.67  thf(t93_zfmisc_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.45/0.67  thf('27', plain,
% 0.45/0.67      (![X30 : $i, X31 : $i]:
% 0.45/0.67         ((k3_tarski @ (k2_tarski @ X30 @ X31)) = (k2_xboole_0 @ X30 @ X31))),
% 0.45/0.67      inference('cnf', [status(esa)], [t93_zfmisc_1])).
% 0.45/0.67  thf('28', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.67      inference('sup+', [status(thm)], ['26', '27'])).
% 0.45/0.67  thf('29', plain,
% 0.45/0.67      (![X30 : $i, X31 : $i]:
% 0.45/0.67         ((k3_tarski @ (k2_tarski @ X30 @ X31)) = (k2_xboole_0 @ X30 @ X31))),
% 0.45/0.67      inference('cnf', [status(esa)], [t93_zfmisc_1])).
% 0.45/0.67  thf('30', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.67      inference('sup+', [status(thm)], ['28', '29'])).
% 0.45/0.67  thf(t41_enumset1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( k2_tarski @ A @ B ) =
% 0.45/0.67       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.45/0.67  thf('31', plain,
% 0.45/0.67      (![X13 : $i, X14 : $i]:
% 0.45/0.67         ((k2_tarski @ X13 @ X14)
% 0.45/0.67           = (k2_xboole_0 @ (k1_tarski @ X13) @ (k1_tarski @ X14)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.45/0.67  thf('32', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k2_tarski @ X0 @ X1)
% 0.45/0.67           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['30', '31'])).
% 0.45/0.67  thf('33', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k2_tarski @ X1 @ X0)
% 0.45/0.67           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X1)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['25', '32'])).
% 0.45/0.67  thf('34', plain,
% 0.45/0.67      (![X33 : $i, X34 : $i]:
% 0.45/0.67         (v1_relat_1 @ (k1_tarski @ (k4_tarski @ X33 @ X34)))),
% 0.45/0.67      inference('cnf', [status(esa)], [fc5_relat_1])).
% 0.45/0.67  thf('35', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k3_relat_1 @ (k1_tarski @ (k4_tarski @ X0 @ X1)))
% 0.45/0.67           = (k2_tarski @ X1 @ X0))),
% 0.45/0.67      inference('demod', [status(thm)], ['13', '24', '33', '34'])).
% 0.45/0.67  thf('36', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.45/0.67      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.45/0.67  thf('37', plain, (((k2_tarski @ sk_A @ sk_B) != (k2_tarski @ sk_A @ sk_B))),
% 0.45/0.67      inference('demod', [status(thm)], ['0', '35', '36'])).
% 0.45/0.67  thf('38', plain, ($false), inference('simplify', [status(thm)], ['37'])).
% 0.45/0.67  
% 0.45/0.67  % SZS output end Refutation
% 0.45/0.67  
% 0.45/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
