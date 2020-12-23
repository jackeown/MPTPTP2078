%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yS9HC72qOJ

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 150 expanded)
%              Number of leaves         :   11 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  332 (1532 expanded)
%              Number of equality atoms :   26 ( 126 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t73_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = k1_xboole_0 )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = k1_xboole_0 )
      <=> ( ( r2_hidden @ A @ C )
          & ( r2_hidden @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( ( k4_xboole_0 @ X6 @ X7 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('6',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( r2_hidden @ X31 @ X32 )
      | ~ ( r1_tarski @ ( k2_tarski @ X31 @ X33 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('9',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('11',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('13',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( r2_hidden @ X33 @ X32 )
      | ~ ( r1_tarski @ ( k2_tarski @ X31 @ X33 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('14',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('16',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['3','11','16','17'])).

thf('19',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['1','18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('23',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['3','11','16','22'])).

thf('24',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X31: $i,X33: $i,X34: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X31 @ X33 ) @ X34 )
      | ~ ( r2_hidden @ X33 @ X34 )
      | ~ ( r2_hidden @ X31 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X6: $i,X8: $i] :
      ( ( ( k4_xboole_0 @ X6 @ X8 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('29',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('31',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['3','11','16'])).

thf('32',plain,(
    ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['30','31'])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['29','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yS9HC72qOJ
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:09:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 195 iterations in 0.070s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(t73_zfmisc_1, conjecture,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.54       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.54        ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.54          ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t73_zfmisc_1])).
% 0.20/0.54  thf('0', plain,
% 0.20/0.54      (((r2_hidden @ sk_A @ sk_C_1)
% 0.20/0.54        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (((r2_hidden @ sk_A @ sk_C_1)) <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      ((~ (r2_hidden @ sk_B @ sk_C_1)
% 0.20/0.54        | ~ (r2_hidden @ sk_A @ sk_C_1)
% 0.20/0.54        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) != (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0))) | 
% 0.20/0.54       ~ ((r2_hidden @ sk_B @ sk_C_1)) | ~ ((r2_hidden @ sk_A @ sk_C_1))),
% 0.20/0.54      inference('split', [status(esa)], ['2'])).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))
% 0.20/0.54         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.20/0.54                = (k1_xboole_0))))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf(t37_xboole_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X6 : $i, X7 : $i]:
% 0.20/0.54         ((r1_tarski @ X6 @ X7) | ((k4_xboole_0 @ X6 @ X7) != (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.54         | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))
% 0.20/0.54         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.20/0.54                = (k1_xboole_0))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.20/0.54         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.20/0.54                = (k1_xboole_0))))),
% 0.20/0.54      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.54  thf(t38_zfmisc_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.20/0.54       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.54         ((r2_hidden @ X31 @ X32)
% 0.20/0.54          | ~ (r1_tarski @ (k2_tarski @ X31 @ X33) @ X32))),
% 0.20/0.54      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (((r2_hidden @ sk_A @ sk_C_1))
% 0.20/0.54         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.20/0.54                = (k1_xboole_0))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      ((~ (r2_hidden @ sk_A @ sk_C_1)) <= (~ ((r2_hidden @ sk_A @ sk_C_1)))),
% 0.20/0.54      inference('split', [status(esa)], ['2'])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (((r2_hidden @ sk_A @ sk_C_1)) | 
% 0.20/0.54       ~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.20/0.54         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.20/0.54                = (k1_xboole_0))))),
% 0.20/0.54      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.54         ((r2_hidden @ X33 @ X32)
% 0.20/0.54          | ~ (r1_tarski @ (k2_tarski @ X31 @ X33) @ X32))),
% 0.20/0.54      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (((r2_hidden @ sk_B @ sk_C_1))
% 0.20/0.54         <= ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.20/0.54                = (k1_xboole_0))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      ((~ (r2_hidden @ sk_B @ sk_C_1)) <= (~ ((r2_hidden @ sk_B @ sk_C_1)))),
% 0.20/0.54      inference('split', [status(esa)], ['2'])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (((r2_hidden @ sk_B @ sk_C_1)) | 
% 0.20/0.54       ~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (((r2_hidden @ sk_A @ sk_C_1)) | 
% 0.20/0.54       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf('18', plain, (((r2_hidden @ sk_A @ sk_C_1))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['3', '11', '16', '17'])).
% 0.20/0.54  thf('19', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['1', '18'])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (((r2_hidden @ sk_B @ sk_C_1)
% 0.20/0.54        | ((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (((r2_hidden @ sk_B @ sk_C_1)) <= (((r2_hidden @ sk_B @ sk_C_1)))),
% 0.20/0.54      inference('split', [status(esa)], ['20'])).
% 0.20/0.54  thf('22', plain,
% 0.20/0.54      (((r2_hidden @ sk_B @ sk_C_1)) | 
% 0.20/0.54       (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.20/0.54      inference('split', [status(esa)], ['20'])).
% 0.20/0.54  thf('23', plain, (((r2_hidden @ sk_B @ sk_C_1))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['3', '11', '16', '22'])).
% 0.20/0.54  thf('24', plain, ((r2_hidden @ sk_B @ sk_C_1)),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['21', '23'])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      (![X31 : $i, X33 : $i, X34 : $i]:
% 0.20/0.54         ((r1_tarski @ (k2_tarski @ X31 @ X33) @ X34)
% 0.20/0.54          | ~ (r2_hidden @ X33 @ X34)
% 0.20/0.54          | ~ (r2_hidden @ X31 @ X34))),
% 0.20/0.54      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X0 @ sk_C_1)
% 0.20/0.54          | (r1_tarski @ (k2_tarski @ X0 @ sk_B) @ sk_C_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.54  thf('27', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 0.20/0.54      inference('sup-', [status(thm)], ['19', '26'])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      (![X6 : $i, X8 : $i]:
% 0.20/0.54         (((k4_xboole_0 @ X6 @ X8) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      ((((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) != (k1_xboole_0)))
% 0.20/0.54         <= (~
% 0.20/0.54             (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.20/0.54                = (k1_xboole_0))))),
% 0.20/0.54      inference('split', [status(esa)], ['2'])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      (~ (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_xboole_0)))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['3', '11', '16'])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) != (k1_xboole_0))),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['30', '31'])).
% 0.20/0.54  thf('33', plain, ($false),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['29', '32'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
