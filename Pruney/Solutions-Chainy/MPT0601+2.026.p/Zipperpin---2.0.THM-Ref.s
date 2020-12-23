%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5jRazaHrV1

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 166 expanded)
%              Number of leaves         :   25 (  54 expanded)
%              Depth                    :   19
%              Number of atoms          :  593 (1416 expanded)
%              Number of equality atoms :   61 ( 144 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t205_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
        <=> ( ( k11_relat_1 @ B @ A )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t205_relat_1])).

thf('0',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('3',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('4',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k11_relat_1 @ X11 @ X12 )
        = ( k9_relat_1 @ X11 @ ( k1_tarski @ X12 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k9_relat_1 @ X13 @ X14 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X19 ) @ X20 )
      | ( ( k7_relat_1 @ X19 @ X20 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('15',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('19',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X4 ) @ X6 )
      | ~ ( r2_hidden @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('20',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('21',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X18 @ X17 ) )
        = X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('22',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
        = ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = ( k1_tarski @ sk_A ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
      & ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','24'])).

thf('26',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
      & ( ( k11_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','25'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X9 ) @ X10 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['26','29'])).

thf('31',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','30'])).

thf('32',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['1','31'])).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k11_relat_1 @ X11 @ X12 )
        = ( k9_relat_1 @ X11 @ ( k1_tarski @ X12 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X7 ) @ X8 )
      | ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('35',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r1_xboole_0 @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( ( k7_relat_1 @ X16 @ X15 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['4'])).

thf('38',plain,
    ( ( ( ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k7_relat_1 @ X19 @ X20 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('42',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('47',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['2','30','46'])).

thf('48',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 )
      | ( ( k9_relat_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['33','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['32','55'])).

thf('57',plain,(
    $false ),
    inference(simplify,[status(thm)],['56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5jRazaHrV1
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:33:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 96 iterations in 0.025s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.48  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.21/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(t205_relat_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.21/0.48         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i]:
% 0.21/0.48        ( ( v1_relat_1 @ B ) =>
% 0.21/0.48          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.21/0.48            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))
% 0.21/0.48        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.21/0.48         <= (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.21/0.48       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf(t60_relat_1, axiom,
% 0.21/0.48    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.48     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.48  thf('3', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.21/0.48        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.21/0.48         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('split', [status(esa)], ['4'])).
% 0.21/0.48  thf(d16_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X11 : $i, X12 : $i]:
% 0.21/0.48         (((k11_relat_1 @ X11 @ X12) = (k9_relat_1 @ X11 @ (k1_tarski @ X12)))
% 0.21/0.48          | ~ (v1_relat_1 @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.21/0.48  thf(t151_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.48         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X13 : $i, X14 : $i]:
% 0.21/0.48         (((k9_relat_1 @ X13 @ X14) != (k1_xboole_0))
% 0.21/0.48          | (r1_xboole_0 @ (k1_relat_1 @ X13) @ X14)
% 0.21/0.48          | ~ (v1_relat_1 @ X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((k11_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.21/0.48          | ~ (v1_relat_1 @ X1)
% 0.21/0.48          | ~ (v1_relat_1 @ X1)
% 0.21/0.48          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ (k1_tarski @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ (k1_relat_1 @ X1) @ (k1_tarski @ X0))
% 0.21/0.48          | ~ (v1_relat_1 @ X1)
% 0.21/0.48          | ((k11_relat_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.48         | ~ (v1_relat_1 @ sk_B)
% 0.21/0.48         | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.21/0.48         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['5', '9'])).
% 0.21/0.48  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.48         | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.21/0.48         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A)))
% 0.21/0.48         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.48  thf(t95_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.48         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X19 : $i, X20 : $i]:
% 0.21/0.48         (~ (r1_xboole_0 @ (k1_relat_1 @ X19) @ X20)
% 0.21/0.48          | ((k7_relat_1 @ X19 @ X20) = (k1_xboole_0))
% 0.21/0.48          | ~ (v1_relat_1 @ X19))),
% 0.21/0.48      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (((~ (v1_relat_1 @ sk_B)
% 0.21/0.48         | ((k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))
% 0.21/0.48         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.48  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      ((((k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.21/0.48         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.21/0.48         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf(l1_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X4 : $i, X6 : $i]:
% 0.21/0.48         ((r1_tarski @ (k1_tarski @ X4) @ X6) | ~ (r2_hidden @ X4 @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_B)))
% 0.21/0.48         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.48  thf(t91_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.21/0.48         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X17 : $i, X18 : $i]:
% 0.21/0.48         (~ (r1_tarski @ X17 @ (k1_relat_1 @ X18))
% 0.21/0.48          | ((k1_relat_1 @ (k7_relat_1 @ X18 @ X17)) = (X17))
% 0.21/0.48          | ~ (v1_relat_1 @ X18))),
% 0.21/0.48      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (((~ (v1_relat_1 @ sk_B)
% 0.21/0.48         | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)))
% 0.21/0.48             = (k1_tarski @ sk_A))))
% 0.21/0.48         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.48  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      ((((k1_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)))
% 0.21/0.48          = (k1_tarski @ sk_A)))
% 0.21/0.48         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      ((((k1_relat_1 @ k1_xboole_0) = (k1_tarski @ sk_A)))
% 0.21/0.48         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) & 
% 0.21/0.48             (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup+', [status(thm)], ['17', '24'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      ((((k1_xboole_0) = (k1_tarski @ sk_A)))
% 0.21/0.48         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) & 
% 0.21/0.48             (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.21/0.48      inference('sup+', [status(thm)], ['3', '25'])).
% 0.21/0.48  thf(t1_boole, axiom,
% 0.21/0.48    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.48  thf('27', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.48  thf(t49_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i]:
% 0.21/0.48         ((k2_xboole_0 @ (k1_tarski @ X9) @ X10) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.21/0.48  thf('29', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) | 
% 0.21/0.48       ~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['26', '29'])).
% 0.21/0.48  thf('31', plain, (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['2', '30'])).
% 0.21/0.48  thf('32', plain, (((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['1', '31'])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      (![X11 : $i, X12 : $i]:
% 0.21/0.48         (((k11_relat_1 @ X11 @ X12) = (k9_relat_1 @ X11 @ (k1_tarski @ X12)))
% 0.21/0.48          | ~ (v1_relat_1 @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.21/0.48  thf(l27_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ (k1_tarski @ X7) @ X8) | (r2_hidden @ X7 @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.21/0.48  thf(t187_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.21/0.48           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      (![X15 : $i, X16 : $i]:
% 0.21/0.48         (~ (r1_xboole_0 @ X15 @ (k1_relat_1 @ X16))
% 0.21/0.48          | ((k7_relat_1 @ X16 @ X15) = (k1_xboole_0))
% 0.21/0.48          | ~ (v1_relat_1 @ X16))),
% 0.21/0.48      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | ((k7_relat_1 @ X0 @ (k1_tarski @ X1)) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.21/0.48         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.48      inference('split', [status(esa)], ['4'])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      (((((k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.21/0.48         | ~ (v1_relat_1 @ sk_B)))
% 0.21/0.48         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.48  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      ((((k7_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.21/0.48         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.48      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      (![X19 : $i, X20 : $i]:
% 0.21/0.48         (((k7_relat_1 @ X19 @ X20) != (k1_xboole_0))
% 0.21/0.48          | (r1_xboole_0 @ (k1_relat_1 @ X19) @ X20)
% 0.21/0.48          | ~ (v1_relat_1 @ X19))),
% 0.21/0.48      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.21/0.48  thf('42', plain,
% 0.21/0.48      (((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.48         | ~ (v1_relat_1 @ sk_B)
% 0.21/0.48         | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.21/0.48         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.48  thf('43', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('44', plain,
% 0.21/0.48      (((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.48         | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.21/0.48         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.48      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A)))
% 0.21/0.48         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.21/0.48      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.48  thf('46', plain,
% 0.21/0.48      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) | 
% 0.21/0.48       (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('split', [status(esa)], ['4'])).
% 0.21/0.48  thf('47', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['2', '30', '46'])).
% 0.21/0.48  thf('48', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A))),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['45', '47'])).
% 0.21/0.48  thf('49', plain,
% 0.21/0.48      (![X13 : $i, X14 : $i]:
% 0.21/0.48         (~ (r1_xboole_0 @ (k1_relat_1 @ X13) @ X14)
% 0.21/0.48          | ((k9_relat_1 @ X13 @ X14) = (k1_xboole_0))
% 0.21/0.48          | ~ (v1_relat_1 @ X13))),
% 0.21/0.48      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.21/0.48  thf('50', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.48        | ((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.48  thf('51', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('52', plain,
% 0.21/0.48      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.21/0.48      inference('demod', [status(thm)], ['50', '51'])).
% 0.21/0.48  thf('53', plain,
% 0.21/0.48      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.48      inference('sup+', [status(thm)], ['33', '52'])).
% 0.21/0.48  thf('54', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('55', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.21/0.48      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.48  thf('56', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.48      inference('demod', [status(thm)], ['32', '55'])).
% 0.21/0.48  thf('57', plain, ($false), inference('simplify', [status(thm)], ['56'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
