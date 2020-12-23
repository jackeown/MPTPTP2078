%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4LV0LlcpKf

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 127 expanded)
%              Number of leaves         :   18 (  42 expanded)
%              Depth                    :   13
%              Number of atoms          :  395 (1066 expanded)
%              Number of equality atoms :   25 (  67 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X25 ) @ X26 )
      | ( r2_hidden @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ X27 ) @ X28 )
      | ( ( k10_relat_1 @ X27 @ X28 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t142_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
      <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
        <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t142_funct_1])).

thf('5',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('11',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

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

thf('12',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X24: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('20',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k10_relat_1 @ X27 @ X28 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X27 ) @ X28 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('21',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
   <= ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['7'])).

thf('26',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) )
      & ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) )
    | ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) )
    | ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('31',plain,(
    ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['8','29','30'])).

thf('32',plain,(
    ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['6','31'])).

thf('33',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf('37',plain,(
    ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['8','29'])).

thf('38',plain,(
    ( k10_relat_1 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['36','37'])).

thf('39',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['35','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4LV0LlcpKf
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:18:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 68 iterations in 0.030s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.45  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.45  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.45  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.45  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.45  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.45  thf(l27_zfmisc_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.45  thf('0', plain,
% 0.20/0.45      (![X25 : $i, X26 : $i]:
% 0.20/0.45         ((r1_xboole_0 @ (k1_tarski @ X25) @ X26) | (r2_hidden @ X25 @ X26))),
% 0.20/0.45      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.20/0.45  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.45    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.45  thf('1', plain,
% 0.20/0.45      (![X3 : $i, X4 : $i]:
% 0.20/0.45         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.20/0.45      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.45  thf('2', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.45  thf(t173_relat_1, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ B ) =>
% 0.20/0.45       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.45         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.45  thf('3', plain,
% 0.20/0.45      (![X27 : $i, X28 : $i]:
% 0.20/0.45         (~ (r1_xboole_0 @ (k2_relat_1 @ X27) @ X28)
% 0.20/0.45          | ((k10_relat_1 @ X27 @ X28) = (k1_xboole_0))
% 0.20/0.45          | ~ (v1_relat_1 @ X27))),
% 0.20/0.45      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.20/0.45  thf('4', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         ((r2_hidden @ X0 @ (k2_relat_1 @ X1))
% 0.20/0.45          | ~ (v1_relat_1 @ X1)
% 0.20/0.45          | ((k10_relat_1 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.45  thf(t142_funct_1, conjecture,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ B ) =>
% 0.20/0.45       ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.20/0.45         ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i,B:$i]:
% 0.20/0.45        ( ( v1_relat_1 @ B ) =>
% 0.20/0.45          ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.20/0.45            ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t142_funct_1])).
% 0.20/0.45  thf('5', plain,
% 0.20/0.45      ((((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.20/0.45        | ~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('6', plain,
% 0.20/0.45      ((~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1)))
% 0.20/0.45         <= (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1))))),
% 0.20/0.45      inference('split', [status(esa)], ['5'])).
% 0.20/0.45  thf('7', plain,
% 0.20/0.45      ((((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) != (k1_xboole_0))
% 0.20/0.45        | (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('8', plain,
% 0.20/0.45      (~ (((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))) | 
% 0.20/0.45       ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1)))),
% 0.20/0.45      inference('split', [status(esa)], ['7'])).
% 0.20/0.45  thf('9', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.45  thf(d1_xboole_0, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.45  thf('10', plain,
% 0.20/0.45      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.45      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.45  thf('11', plain,
% 0.20/0.45      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.45      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.45  thf(t3_xboole_0, axiom,
% 0.20/0.45    (![A:$i,B:$i]:
% 0.20/0.45     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.45            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.45       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.45            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.45  thf('12', plain,
% 0.20/0.45      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.20/0.45         (~ (r2_hidden @ X7 @ X5)
% 0.20/0.45          | ~ (r2_hidden @ X7 @ X8)
% 0.20/0.45          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.20/0.45      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.45  thf('13', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         ((v1_xboole_0 @ X0)
% 0.20/0.45          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.20/0.45          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.20/0.45      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.45  thf('14', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         ((v1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X0 @ X0) | (v1_xboole_0 @ X0))),
% 0.20/0.45      inference('sup-', [status(thm)], ['10', '13'])).
% 0.20/0.45  thf('15', plain,
% 0.20/0.45      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (v1_xboole_0 @ X0))),
% 0.20/0.45      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.45  thf('16', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.20/0.45          | (v1_xboole_0 @ (k1_tarski @ X0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['9', '15'])).
% 0.20/0.45  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.20/0.45  thf('17', plain, (![X24 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X24))),
% 0.20/0.45      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.20/0.45  thf('18', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.45      inference('clc', [status(thm)], ['16', '17'])).
% 0.20/0.45  thf('19', plain,
% 0.20/0.45      ((((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.20/0.45         <= ((((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.45      inference('split', [status(esa)], ['5'])).
% 0.20/0.45  thf('20', plain,
% 0.20/0.45      (![X27 : $i, X28 : $i]:
% 0.20/0.45         (((k10_relat_1 @ X27 @ X28) != (k1_xboole_0))
% 0.20/0.45          | (r1_xboole_0 @ (k2_relat_1 @ X27) @ X28)
% 0.20/0.45          | ~ (v1_relat_1 @ X27))),
% 0.20/0.45      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.20/0.45  thf('21', plain,
% 0.20/0.45      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.45         | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.45         | (r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ (k1_tarski @ sk_A))))
% 0.20/0.45         <= ((((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.45      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.45  thf('22', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('23', plain,
% 0.20/0.45      (((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.45         | (r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ (k1_tarski @ sk_A))))
% 0.20/0.45         <= ((((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.45      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.45  thf('24', plain,
% 0.20/0.45      (((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ (k1_tarski @ sk_A)))
% 0.20/0.45         <= ((((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.45      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.45  thf('25', plain,
% 0.20/0.45      (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1)))
% 0.20/0.45         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1))))),
% 0.20/0.45      inference('split', [status(esa)], ['7'])).
% 0.20/0.45  thf('26', plain,
% 0.20/0.45      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.20/0.45         (~ (r2_hidden @ X7 @ X5)
% 0.20/0.45          | ~ (r2_hidden @ X7 @ X8)
% 0.20/0.45          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.20/0.45      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.45  thf('27', plain,
% 0.20/0.45      ((![X0 : $i]:
% 0.20/0.45          (~ (r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ X0)
% 0.20/0.45           | ~ (r2_hidden @ sk_A @ X0)))
% 0.20/0.45         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1))))),
% 0.20/0.45      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.45  thf('28', plain,
% 0.20/0.45      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))
% 0.20/0.45         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1))) & 
% 0.20/0.45             (((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.45      inference('sup-', [status(thm)], ['24', '27'])).
% 0.20/0.45  thf('29', plain,
% 0.20/0.45      (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1))) | 
% 0.20/0.45       ~ (((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0)))),
% 0.20/0.45      inference('sup-', [status(thm)], ['18', '28'])).
% 0.20/0.45  thf('30', plain,
% 0.20/0.45      (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1))) | 
% 0.20/0.45       (((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0)))),
% 0.20/0.45      inference('split', [status(esa)], ['5'])).
% 0.20/0.45  thf('31', plain, (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1)))),
% 0.20/0.45      inference('sat_resolution*', [status(thm)], ['8', '29', '30'])).
% 0.20/0.45  thf('32', plain, (~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B_1))),
% 0.20/0.45      inference('simpl_trail', [status(thm)], ['6', '31'])).
% 0.20/0.45  thf('33', plain,
% 0.20/0.45      ((((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.20/0.45        | ~ (v1_relat_1 @ sk_B_1))),
% 0.20/0.45      inference('sup-', [status(thm)], ['4', '32'])).
% 0.20/0.45  thf('34', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('35', plain,
% 0.20/0.45      (((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.20/0.45      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.45  thf('36', plain,
% 0.20/0.45      ((((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) != (k1_xboole_0)))
% 0.20/0.45         <= (~ (((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.20/0.45      inference('split', [status(esa)], ['7'])).
% 0.20/0.45  thf('37', plain,
% 0.20/0.45      (~ (((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0)))),
% 0.20/0.45      inference('sat_resolution*', [status(thm)], ['8', '29'])).
% 0.20/0.45  thf('38', plain,
% 0.20/0.45      (((k10_relat_1 @ sk_B_1 @ (k1_tarski @ sk_A)) != (k1_xboole_0))),
% 0.20/0.45      inference('simpl_trail', [status(thm)], ['36', '37'])).
% 0.20/0.45  thf('39', plain, ($false),
% 0.20/0.45      inference('simplify_reflect-', [status(thm)], ['35', '38'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
