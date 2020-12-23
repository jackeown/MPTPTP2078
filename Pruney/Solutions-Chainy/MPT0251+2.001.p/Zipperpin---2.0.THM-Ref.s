%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bRjb52TQnl

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:01 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 127 expanded)
%              Number of leaves         :   26 (  51 expanded)
%              Depth                    :   16
%              Number of atoms          :  458 ( 808 expanded)
%              Number of equality atoms :   48 (  91 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X51: $i,X53: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X51 ) @ X53 )
      | ~ ( r2_hidden @ X51 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('7',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k2_tarski @ X35 @ X34 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X54 @ X55 ) )
      = ( k2_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X54: $i,X55: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X54 @ X55 ) )
      = ( k2_xboole_0 @ X54 @ X55 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X27 @ X28 ) @ X28 )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_tarski @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ X21 )
      = ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['15','22'])).

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

thf('24',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) )
      = ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('30',plain,(
    ! [X31: $i,X33: $i] :
      ( ( r1_xboole_0 @ X31 @ X33 )
      | ( ( k4_xboole_0 @ X31 @ X33 )
       != X31 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 != X0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('34',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_tarski @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('35',plain,(
    ! [X51: $i,X52: $i] :
      ( ( r2_hidden @ X51 @ X52 )
      | ~ ( r1_tarski @ ( k1_tarski @ X51 ) @ X52 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X2 )
      | ~ ( r2_hidden @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['24','40'])).

thf('42',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k4_xboole_0 @ X31 @ X32 )
        = X31 )
      | ~ ( r1_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','43'])).

thf('45',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','44'])).

thf('46',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_xboole_0 @ X25 @ ( k4_xboole_0 @ X26 @ X25 ) )
      = ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('47',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('49',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('52',plain,(
    ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
 != sk_B_1 ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['49','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bRjb52TQnl
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 18:18:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.39/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.61  % Solved by: fo/fo7.sh
% 0.39/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.61  % done 388 iterations in 0.132s
% 0.39/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.61  % SZS output start Refutation
% 0.39/0.61  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.39/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.39/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.61  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.39/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.61  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.39/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.61  thf(t46_zfmisc_1, conjecture,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( r2_hidden @ A @ B ) =>
% 0.39/0.61       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.39/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.61    (~( ![A:$i,B:$i]:
% 0.39/0.61        ( ( r2_hidden @ A @ B ) =>
% 0.39/0.61          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.39/0.61    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.39/0.61  thf('0', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf(l1_zfmisc_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.39/0.61  thf('1', plain,
% 0.39/0.61      (![X51 : $i, X53 : $i]:
% 0.39/0.61         ((r1_tarski @ (k1_tarski @ X51) @ X53) | ~ (r2_hidden @ X51 @ X53))),
% 0.39/0.61      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.39/0.61  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.39/0.61      inference('sup-', [status(thm)], ['0', '1'])).
% 0.39/0.61  thf(t28_xboole_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.39/0.61  thf('3', plain,
% 0.39/0.61      (![X23 : $i, X24 : $i]:
% 0.39/0.61         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.39/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.61  thf('4', plain,
% 0.39/0.61      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))),
% 0.39/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.61  thf(t100_xboole_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.39/0.61  thf('5', plain,
% 0.39/0.61      (![X20 : $i, X21 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X20 @ X21)
% 0.39/0.61           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.39/0.61  thf('6', plain,
% 0.39/0.61      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.39/0.61         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.39/0.61      inference('sup+', [status(thm)], ['4', '5'])).
% 0.39/0.61  thf(commutativity_k2_tarski, axiom,
% 0.39/0.61    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.39/0.61  thf('7', plain,
% 0.39/0.61      (![X34 : $i, X35 : $i]:
% 0.39/0.61         ((k2_tarski @ X35 @ X34) = (k2_tarski @ X34 @ X35))),
% 0.39/0.61      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.39/0.61  thf(l51_zfmisc_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.61  thf('8', plain,
% 0.39/0.61      (![X54 : $i, X55 : $i]:
% 0.39/0.61         ((k3_tarski @ (k2_tarski @ X54 @ X55)) = (k2_xboole_0 @ X54 @ X55))),
% 0.39/0.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.39/0.61  thf('9', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.61      inference('sup+', [status(thm)], ['7', '8'])).
% 0.39/0.61  thf('10', plain,
% 0.39/0.61      (![X54 : $i, X55 : $i]:
% 0.39/0.61         ((k3_tarski @ (k2_tarski @ X54 @ X55)) = (k2_xboole_0 @ X54 @ X55))),
% 0.39/0.61      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.39/0.61  thf('11', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.61      inference('sup+', [status(thm)], ['9', '10'])).
% 0.39/0.61  thf(t1_boole, axiom,
% 0.39/0.61    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.39/0.61  thf('12', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.39/0.61      inference('cnf', [status(esa)], [t1_boole])).
% 0.39/0.61  thf('13', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.61      inference('sup+', [status(thm)], ['11', '12'])).
% 0.39/0.61  thf(t40_xboole_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.39/0.61  thf('14', plain,
% 0.39/0.61      (![X27 : $i, X28 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ (k2_xboole_0 @ X27 @ X28) @ X28)
% 0.39/0.61           = (k4_xboole_0 @ X27 @ X28))),
% 0.39/0.61      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.39/0.61  thf('15', plain,
% 0.39/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.39/0.61      inference('sup+', [status(thm)], ['13', '14'])).
% 0.39/0.61  thf('16', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.39/0.61      inference('cnf', [status(esa)], [t1_boole])).
% 0.39/0.61  thf(t7_xboole_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.61  thf('17', plain,
% 0.39/0.61      (![X29 : $i, X30 : $i]: (r1_tarski @ X29 @ (k2_xboole_0 @ X29 @ X30))),
% 0.39/0.61      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.39/0.61  thf('18', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.39/0.61      inference('sup+', [status(thm)], ['16', '17'])).
% 0.39/0.61  thf('19', plain,
% 0.39/0.61      (![X23 : $i, X24 : $i]:
% 0.39/0.61         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 0.39/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.61  thf('20', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.39/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.61  thf('21', plain,
% 0.39/0.61      (![X20 : $i, X21 : $i]:
% 0.39/0.61         ((k4_xboole_0 @ X20 @ X21)
% 0.39/0.61           = (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.39/0.61  thf('22', plain,
% 0.39/0.61      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.39/0.61      inference('sup+', [status(thm)], ['20', '21'])).
% 0.39/0.61  thf('23', plain,
% 0.39/0.61      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.39/0.61      inference('demod', [status(thm)], ['15', '22'])).
% 0.39/0.61  thf(t3_xboole_0, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.39/0.61            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.39/0.61       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.39/0.61            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.39/0.62  thf('24', plain,
% 0.39/0.62      (![X9 : $i, X10 : $i]:
% 0.39/0.62         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C_1 @ X10 @ X9) @ X9))),
% 0.39/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.39/0.62  thf(t39_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.39/0.62  thf('25', plain,
% 0.39/0.62      (![X25 : $i, X26 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25))
% 0.39/0.62           = (k2_xboole_0 @ X25 @ X26))),
% 0.39/0.62      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.62  thf('26', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['11', '12'])).
% 0.39/0.62  thf('27', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['25', '26'])).
% 0.39/0.62  thf('28', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['11', '12'])).
% 0.39/0.62  thf('29', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['27', '28'])).
% 0.39/0.62  thf(t83_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.39/0.62  thf('30', plain,
% 0.39/0.62      (![X31 : $i, X33 : $i]:
% 0.39/0.62         ((r1_xboole_0 @ X31 @ X33) | ((k4_xboole_0 @ X31 @ X33) != (X31)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.39/0.62  thf('31', plain,
% 0.39/0.62      (![X0 : $i]: (((X0) != (X0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['29', '30'])).
% 0.39/0.62  thf('32', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.39/0.62      inference('simplify', [status(thm)], ['31'])).
% 0.39/0.62  thf('33', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.62      inference('sup+', [status(thm)], ['9', '10'])).
% 0.39/0.62  thf('34', plain,
% 0.39/0.62      (![X29 : $i, X30 : $i]: (r1_tarski @ X29 @ (k2_xboole_0 @ X29 @ X30))),
% 0.39/0.62      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.39/0.62  thf('35', plain,
% 0.39/0.62      (![X51 : $i, X52 : $i]:
% 0.39/0.62         ((r2_hidden @ X51 @ X52) | ~ (r1_tarski @ (k1_tarski @ X51) @ X52))),
% 0.39/0.62      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.39/0.62  thf('36', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (r2_hidden @ X1 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.39/0.62  thf('37', plain,
% 0.39/0.62      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X11 @ X9)
% 0.39/0.62          | ~ (r2_hidden @ X11 @ X12)
% 0.39/0.62          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.39/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.39/0.62  thf('38', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         (~ (r1_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0) @ X2)
% 0.39/0.62          | ~ (r2_hidden @ X1 @ X2))),
% 0.39/0.62      inference('sup-', [status(thm)], ['36', '37'])).
% 0.39/0.62  thf('39', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         (~ (r1_xboole_0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)) @ X2)
% 0.39/0.62          | ~ (r2_hidden @ X0 @ X2))),
% 0.39/0.62      inference('sup-', [status(thm)], ['33', '38'])).
% 0.39/0.62  thf('40', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.39/0.62      inference('sup-', [status(thm)], ['32', '39'])).
% 0.39/0.62  thf('41', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.39/0.62      inference('sup-', [status(thm)], ['24', '40'])).
% 0.39/0.62  thf('42', plain,
% 0.39/0.62      (![X31 : $i, X32 : $i]:
% 0.39/0.62         (((k4_xboole_0 @ X31 @ X32) = (X31)) | ~ (r1_xboole_0 @ X31 @ X32))),
% 0.39/0.62      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.39/0.62  thf('43', plain,
% 0.39/0.62      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['41', '42'])).
% 0.39/0.62  thf('44', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.39/0.62      inference('demod', [status(thm)], ['23', '43'])).
% 0.39/0.62  thf('45', plain,
% 0.39/0.62      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))),
% 0.39/0.62      inference('demod', [status(thm)], ['6', '44'])).
% 0.39/0.62  thf('46', plain,
% 0.39/0.62      (![X25 : $i, X26 : $i]:
% 0.39/0.62         ((k2_xboole_0 @ X25 @ (k4_xboole_0 @ X26 @ X25))
% 0.39/0.62           = (k2_xboole_0 @ X25 @ X26))),
% 0.39/0.62      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.39/0.62  thf('47', plain,
% 0.39/0.62      (((k2_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 0.39/0.62         = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.39/0.62      inference('sup+', [status(thm)], ['45', '46'])).
% 0.39/0.62  thf('48', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 0.39/0.62      inference('cnf', [status(esa)], [t1_boole])).
% 0.39/0.62  thf('49', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.39/0.62      inference('demod', [status(thm)], ['47', '48'])).
% 0.39/0.62  thf('50', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (sk_B_1))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('51', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.62      inference('sup+', [status(thm)], ['9', '10'])).
% 0.39/0.62  thf('52', plain, (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) != (sk_B_1))),
% 0.39/0.62      inference('demod', [status(thm)], ['50', '51'])).
% 0.39/0.62  thf('53', plain, ($false),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['49', '52'])).
% 0.39/0.62  
% 0.39/0.62  % SZS output end Refutation
% 0.39/0.62  
% 0.39/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
