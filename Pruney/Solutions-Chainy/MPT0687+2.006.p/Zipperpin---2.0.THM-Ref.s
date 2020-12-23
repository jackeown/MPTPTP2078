%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.amoZv6zW6K

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:11 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 175 expanded)
%              Number of leaves         :   22 (  54 expanded)
%              Depth                    :   17
%              Number of atoms          :  548 (1658 expanded)
%              Number of equality atoms :   53 ( 161 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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

thf('0',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ( X15 = X12 )
      | ( X14
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X12: $i,X15: $i] :
      ( ( X15 = X12 )
      | ~ ( r2_hidden @ X15 @ ( k1_tarski @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('7',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ X25 ) @ X26 )
      | ( ( k10_relat_1 @ X25 @ X26 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

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

thf('9',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('14',plain,
    ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['11'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('15',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X17 ) @ X19 )
      | ~ ( r2_hidden @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('16',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t174_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
          & ( ( k10_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf('17',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X27 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X28 )
      | ~ ( r1_tarski @ X27 @ ( k2_relat_1 @ X28 ) )
      | ( ( k10_relat_1 @ X28 @ X27 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t174_relat_1])).

thf('18',plain,
    ( ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
       != k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(l29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('23',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ X21 )
      | ( ( k3_xboole_0 @ X21 @ ( k1_tarski @ X20 ) )
       != ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[l29_zfmisc_1])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
         != ( k1_tarski @ sk_A ) )
        | ( r2_hidden @ sk_A @ X0 ) )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('26',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( r2_hidden @ sk_A @ X0 ) )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_A @ X0 )
   <= ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
      & ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('30',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k3_xboole_0 @ X7 @ X10 ) )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('33',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','35'])).

thf('37',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','36'])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('39',plain,(
    ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['12','37','38'])).

thf('40',plain,(
    ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['10','39'])).

thf('41',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('45',plain,(
    ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['12','37'])).

thf('46',plain,(
    ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['43','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.amoZv6zW6K
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:39:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.34/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.34/0.54  % Solved by: fo/fo7.sh
% 0.34/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.54  % done 99 iterations in 0.044s
% 0.34/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.34/0.54  % SZS output start Refutation
% 0.34/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.34/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.34/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.34/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.34/0.54  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.34/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.34/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.34/0.54  thf(t3_xboole_0, axiom,
% 0.34/0.54    (![A:$i,B:$i]:
% 0.34/0.54     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.34/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.34/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.34/0.54            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.34/0.54  thf('0', plain,
% 0.34/0.54      (![X3 : $i, X4 : $i]:
% 0.34/0.54         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.34/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.34/0.54  thf(d1_tarski, axiom,
% 0.34/0.54    (![A:$i,B:$i]:
% 0.34/0.54     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.34/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.34/0.54  thf('1', plain,
% 0.34/0.54      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.34/0.54         (~ (r2_hidden @ X15 @ X14)
% 0.34/0.54          | ((X15) = (X12))
% 0.34/0.54          | ((X14) != (k1_tarski @ X12)))),
% 0.34/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.34/0.54  thf('2', plain,
% 0.34/0.54      (![X12 : $i, X15 : $i]:
% 0.34/0.54         (((X15) = (X12)) | ~ (r2_hidden @ X15 @ (k1_tarski @ X12)))),
% 0.34/0.54      inference('simplify', [status(thm)], ['1'])).
% 0.34/0.54  thf('3', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i]:
% 0.34/0.54         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.34/0.54          | ((sk_C @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.34/0.54      inference('sup-', [status(thm)], ['0', '2'])).
% 0.34/0.54  thf('4', plain,
% 0.34/0.54      (![X3 : $i, X4 : $i]:
% 0.34/0.54         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.34/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.34/0.54  thf('5', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i]:
% 0.34/0.54         ((r2_hidden @ X0 @ X1)
% 0.34/0.54          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0))
% 0.34/0.54          | (r1_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.34/0.54      inference('sup+', [status(thm)], ['3', '4'])).
% 0.34/0.54  thf('6', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i]:
% 0.34/0.54         ((r1_xboole_0 @ X1 @ (k1_tarski @ X0)) | (r2_hidden @ X0 @ X1))),
% 0.34/0.54      inference('simplify', [status(thm)], ['5'])).
% 0.34/0.54  thf(t173_relat_1, axiom,
% 0.34/0.54    (![A:$i,B:$i]:
% 0.34/0.54     ( ( v1_relat_1 @ B ) =>
% 0.34/0.54       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.34/0.54         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.34/0.54  thf('7', plain,
% 0.34/0.54      (![X25 : $i, X26 : $i]:
% 0.34/0.54         (~ (r1_xboole_0 @ (k2_relat_1 @ X25) @ X26)
% 0.34/0.54          | ((k10_relat_1 @ X25 @ X26) = (k1_xboole_0))
% 0.34/0.54          | ~ (v1_relat_1 @ X25))),
% 0.34/0.54      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.34/0.54  thf('8', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i]:
% 0.34/0.54         ((r2_hidden @ X0 @ (k2_relat_1 @ X1))
% 0.34/0.54          | ~ (v1_relat_1 @ X1)
% 0.34/0.54          | ((k10_relat_1 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.34/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.34/0.54  thf(t142_funct_1, conjecture,
% 0.34/0.54    (![A:$i,B:$i]:
% 0.34/0.54     ( ( v1_relat_1 @ B ) =>
% 0.34/0.54       ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.34/0.54         ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.34/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.54    (~( ![A:$i,B:$i]:
% 0.34/0.54        ( ( v1_relat_1 @ B ) =>
% 0.34/0.54          ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.34/0.54            ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.34/0.54    inference('cnf.neg', [status(esa)], [t142_funct_1])).
% 0.34/0.54  thf('9', plain,
% 0.34/0.54      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.34/0.54        | ~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf('10', plain,
% 0.34/0.54      ((~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.34/0.54         <= (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.34/0.54      inference('split', [status(esa)], ['9'])).
% 0.34/0.54  thf('11', plain,
% 0.34/0.54      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0))
% 0.34/0.54        | (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf('12', plain,
% 0.34/0.54      (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))) | 
% 0.34/0.54       ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.34/0.54      inference('split', [status(esa)], ['11'])).
% 0.34/0.54  thf('13', plain,
% 0.34/0.54      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.34/0.54         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.34/0.54      inference('split', [status(esa)], ['9'])).
% 0.34/0.54  thf('14', plain,
% 0.34/0.54      (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.34/0.54         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.34/0.54      inference('split', [status(esa)], ['11'])).
% 0.34/0.54  thf(l1_zfmisc_1, axiom,
% 0.34/0.54    (![A:$i,B:$i]:
% 0.34/0.54     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.34/0.54  thf('15', plain,
% 0.34/0.54      (![X17 : $i, X19 : $i]:
% 0.34/0.54         ((r1_tarski @ (k1_tarski @ X17) @ X19) | ~ (r2_hidden @ X17 @ X19))),
% 0.34/0.54      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.34/0.54  thf('16', plain,
% 0.34/0.54      (((r1_tarski @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_B)))
% 0.34/0.54         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.34/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.34/0.54  thf(t174_relat_1, axiom,
% 0.34/0.54    (![A:$i,B:$i]:
% 0.34/0.54     ( ( v1_relat_1 @ B ) =>
% 0.34/0.54       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.34/0.54            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.34/0.54            ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.34/0.54  thf('17', plain,
% 0.34/0.54      (![X27 : $i, X28 : $i]:
% 0.34/0.54         (((X27) = (k1_xboole_0))
% 0.34/0.54          | ~ (v1_relat_1 @ X28)
% 0.34/0.54          | ~ (r1_tarski @ X27 @ (k2_relat_1 @ X28))
% 0.34/0.54          | ((k10_relat_1 @ X28 @ X27) != (k1_xboole_0)))),
% 0.34/0.54      inference('cnf', [status(esa)], [t174_relat_1])).
% 0.34/0.54  thf('18', plain,
% 0.34/0.54      (((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0))
% 0.34/0.54         | ~ (v1_relat_1 @ sk_B)
% 0.34/0.54         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.34/0.54         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.34/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.34/0.54  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf('20', plain,
% 0.34/0.54      (((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0))
% 0.34/0.54         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.34/0.54         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.34/0.54      inference('demod', [status(thm)], ['18', '19'])).
% 0.34/0.54  thf('21', plain,
% 0.34/0.54      (((((k1_xboole_0) != (k1_xboole_0))
% 0.34/0.54         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.34/0.54         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.34/0.54             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.34/0.54      inference('sup-', [status(thm)], ['13', '20'])).
% 0.34/0.54  thf('22', plain,
% 0.34/0.54      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.34/0.54         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.34/0.54             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.34/0.54      inference('simplify', [status(thm)], ['21'])).
% 0.34/0.54  thf(l29_zfmisc_1, axiom,
% 0.34/0.54    (![A:$i,B:$i]:
% 0.34/0.54     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.34/0.54       ( r2_hidden @ B @ A ) ))).
% 0.34/0.54  thf('23', plain,
% 0.34/0.54      (![X20 : $i, X21 : $i]:
% 0.34/0.54         ((r2_hidden @ X20 @ X21)
% 0.34/0.54          | ((k3_xboole_0 @ X21 @ (k1_tarski @ X20)) != (k1_tarski @ X20)))),
% 0.34/0.54      inference('cnf', [status(esa)], [l29_zfmisc_1])).
% 0.34/0.54  thf('24', plain,
% 0.34/0.54      ((![X0 : $i]:
% 0.34/0.54          (((k3_xboole_0 @ X0 @ k1_xboole_0) != (k1_tarski @ sk_A))
% 0.34/0.54           | (r2_hidden @ sk_A @ X0)))
% 0.34/0.54         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.34/0.54             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.34/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.34/0.54  thf(t2_boole, axiom,
% 0.34/0.54    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.34/0.54  thf('25', plain,
% 0.34/0.54      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.54      inference('cnf', [status(esa)], [t2_boole])).
% 0.34/0.54  thf('26', plain,
% 0.34/0.54      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.34/0.54         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.34/0.54             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.34/0.54      inference('simplify', [status(thm)], ['21'])).
% 0.34/0.54  thf('27', plain,
% 0.34/0.54      ((![X0 : $i]:
% 0.34/0.54          (((k1_xboole_0) != (k1_xboole_0)) | (r2_hidden @ sk_A @ X0)))
% 0.34/0.54         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.34/0.54             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.34/0.54      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.34/0.54  thf('28', plain,
% 0.34/0.54      ((![X0 : $i]: (r2_hidden @ sk_A @ X0))
% 0.34/0.54         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) & 
% 0.34/0.54             (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.34/0.54      inference('simplify', [status(thm)], ['27'])).
% 0.34/0.54  thf('29', plain,
% 0.34/0.54      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.54      inference('cnf', [status(esa)], [t2_boole])).
% 0.34/0.54  thf(t4_xboole_0, axiom,
% 0.34/0.54    (![A:$i,B:$i]:
% 0.34/0.54     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.34/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.34/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.34/0.54            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.34/0.54  thf('30', plain,
% 0.34/0.54      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.34/0.54         (~ (r2_hidden @ X9 @ (k3_xboole_0 @ X7 @ X10))
% 0.34/0.54          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.34/0.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.34/0.54  thf('31', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i]:
% 0.34/0.54         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.34/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.34/0.54  thf('32', plain,
% 0.34/0.54      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.54      inference('cnf', [status(esa)], [t2_boole])).
% 0.34/0.54  thf(d7_xboole_0, axiom,
% 0.34/0.54    (![A:$i,B:$i]:
% 0.34/0.54     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.34/0.54       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.34/0.54  thf('33', plain,
% 0.34/0.54      (![X0 : $i, X2 : $i]:
% 0.34/0.54         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.34/0.54      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.34/0.54  thf('34', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.34/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.34/0.54  thf('35', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.34/0.54      inference('simplify', [status(thm)], ['34'])).
% 0.34/0.54  thf('36', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.34/0.54      inference('demod', [status(thm)], ['31', '35'])).
% 0.34/0.54  thf('37', plain,
% 0.34/0.54      (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) | 
% 0.34/0.54       ~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))),
% 0.34/0.54      inference('sup-', [status(thm)], ['28', '36'])).
% 0.34/0.54  thf('38', plain,
% 0.34/0.54      (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))) | 
% 0.34/0.54       (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))),
% 0.34/0.54      inference('split', [status(esa)], ['9'])).
% 0.34/0.54  thf('39', plain, (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.34/0.54      inference('sat_resolution*', [status(thm)], ['12', '37', '38'])).
% 0.34/0.54  thf('40', plain, (~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.34/0.54      inference('simpl_trail', [status(thm)], ['10', '39'])).
% 0.34/0.54  thf('41', plain,
% 0.34/0.54      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.34/0.54        | ~ (v1_relat_1 @ sk_B))),
% 0.34/0.54      inference('sup-', [status(thm)], ['8', '40'])).
% 0.34/0.54  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf('43', plain,
% 0.34/0.54      (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 0.34/0.54      inference('demod', [status(thm)], ['41', '42'])).
% 0.34/0.54  thf('44', plain,
% 0.34/0.54      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0)))
% 0.34/0.54         <= (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.34/0.54      inference('split', [status(esa)], ['11'])).
% 0.34/0.54  thf('45', plain,
% 0.34/0.54      (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))),
% 0.34/0.54      inference('sat_resolution*', [status(thm)], ['12', '37'])).
% 0.34/0.54  thf('46', plain,
% 0.34/0.54      (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0))),
% 0.34/0.54      inference('simpl_trail', [status(thm)], ['44', '45'])).
% 0.34/0.54  thf('47', plain, ($false),
% 0.34/0.54      inference('simplify_reflect-', [status(thm)], ['43', '46'])).
% 0.34/0.54  
% 0.34/0.54  % SZS output end Refutation
% 0.34/0.54  
% 0.34/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
