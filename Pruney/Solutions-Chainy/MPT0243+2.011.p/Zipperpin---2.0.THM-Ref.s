%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oYapLoFrcQ

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 106 expanded)
%              Number of leaves         :   22 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :  507 ( 919 expanded)
%              Number of equality atoms :   20 (  32 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t38_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ C )
          & ( r2_hidden @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_enumset1 @ X25 @ X25 @ X26 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 )
      | ( r2_hidden @ X16 @ X20 )
      | ( X20
       != ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X16 @ ( k1_enumset1 @ X19 @ X18 @ X17 ) )
      | ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X13 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ~ ( zip_tseitin_0 @ X13 @ X13 @ X14 @ X11 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['9'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,
    ( ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
      = ( k2_tarski @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('14',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
        | ( r2_hidden @ X0 @ sk_C ) )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    | ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['17'])).

thf('21',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('22',plain,(
    ! [X30: $i,X32: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X30 ) @ X32 )
      | ~ ( r2_hidden @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('23',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_C )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['9'])).

thf('25',plain,(
    ! [X30: $i,X32: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X30 ) @ X32 )
      | ~ ( r2_hidden @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('26',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('27',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X9 )
      | ( r1_tarski @ ( k2_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) @ sk_C )
        | ~ ( r1_tarski @ X0 @ sk_C ) )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ sk_C )
   <= ( ( r2_hidden @ sk_A @ sk_C )
      & ( r2_hidden @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('30',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_tarski @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k1_tarski @ X23 ) @ ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('31',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( ( r2_hidden @ sk_A @ sk_C )
      & ( r2_hidden @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['17'])).

thf('33',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    | ~ ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['9'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X11 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('37',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ~ ( zip_tseitin_0 @ X11 @ X13 @ X14 @ X11 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
        | ( r2_hidden @ X0 @ sk_C ) )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('40',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['17'])).

thf('42',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','19','20','33','34','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oYapLoFrcQ
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 156 iterations in 0.042s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(t38_zfmisc_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.20/0.51       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.51        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.20/0.51          ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t38_zfmisc_1])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ sk_C)
% 0.20/0.51        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)) | 
% 0.20/0.51       ((r2_hidden @ sk_B @ sk_C))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf(t70_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X25 : $i, X26 : $i]:
% 0.20/0.51         ((k1_enumset1 @ X25 @ X25 @ X26) = (k2_tarski @ X25 @ X26))),
% 0.20/0.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.51  thf(d1_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.51       ( ![E:$i]:
% 0.20/0.51         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.51           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.51  thf(zf_stmt_2, axiom,
% 0.20/0.51    (![E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.51     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.20/0.51       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_3, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.51       ( ![E:$i]:
% 0.20/0.51         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.51         ((zip_tseitin_0 @ X16 @ X17 @ X18 @ X19)
% 0.20/0.51          | (r2_hidden @ X16 @ X20)
% 0.20/0.51          | ((X20) != (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.51         ((r2_hidden @ X16 @ (k1_enumset1 @ X19 @ X18 @ X17))
% 0.20/0.51          | (zip_tseitin_0 @ X16 @ X17 @ X18 @ X19))),
% 0.20/0.51      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.51          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.51      inference('sup+', [status(thm)], ['2', '4'])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.51         (((X12) != (X13)) | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.20/0.51         ~ (zip_tseitin_0 @ X13 @ X13 @ X14 @ X11)),
% 0.20/0.51      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '7'])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (((r2_hidden @ sk_A @ sk_C)
% 0.20/0.51        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.20/0.51         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.20/0.51      inference('split', [status(esa)], ['9'])).
% 0.20/0.51  thf(t28_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      ((((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)
% 0.20/0.51          = (k2_tarski @ sk_A @ sk_B)))
% 0.20/0.51         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf(d4_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.20/0.51       ( ![D:$i]:
% 0.20/0.51         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.51           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X4 @ X3)
% 0.20/0.51          | (r2_hidden @ X4 @ X2)
% 0.20/0.51          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.20/0.51         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.20/0.51           | (r2_hidden @ X0 @ sk_C)))
% 0.20/0.51         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '14'])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ sk_C))
% 0.20/0.51         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['8', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_B @ sk_C)
% 0.20/0.51        | ~ (r2_hidden @ sk_A @ sk_C)
% 0.20/0.51        | ~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_B @ sk_C)) <= (~ ((r2_hidden @ sk_B @ sk_C)))),
% 0.20/0.51      inference('split', [status(esa)], ['17'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)) | 
% 0.20/0.51       ((r2_hidden @ sk_B @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['16', '18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (~ ((r2_hidden @ sk_A @ sk_C)) | 
% 0.20/0.51       ~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)) | 
% 0.20/0.51       ~ ((r2_hidden @ sk_B @ sk_C))),
% 0.20/0.51      inference('split', [status(esa)], ['17'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (((r2_hidden @ sk_B @ sk_C)) <= (((r2_hidden @ sk_B @ sk_C)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf(l1_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X30 : $i, X32 : $i]:
% 0.20/0.51         ((r1_tarski @ (k1_tarski @ X30) @ X32) | ~ (r2_hidden @ X30 @ X32))),
% 0.20/0.51      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (((r1_tarski @ (k1_tarski @ sk_B) @ sk_C))
% 0.20/0.51         <= (((r2_hidden @ sk_B @ sk_C)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.20/0.51      inference('split', [status(esa)], ['9'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X30 : $i, X32 : $i]:
% 0.20/0.51         ((r1_tarski @ (k1_tarski @ X30) @ X32) | ~ (r2_hidden @ X30 @ X32))),
% 0.20/0.51      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_C))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf(t8_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.20/0.51       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.51         (~ (r1_tarski @ X8 @ X9)
% 0.20/0.51          | ~ (r1_tarski @ X10 @ X9)
% 0.20/0.51          | (r1_tarski @ (k2_xboole_0 @ X8 @ X10) @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ X0) @ sk_C)
% 0.20/0.51           | ~ (r1_tarski @ X0 @ sk_C)))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ 
% 0.20/0.51         sk_C)) <= (((r2_hidden @ sk_A @ sk_C)) & ((r2_hidden @ sk_B @ sk_C)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['23', '28'])).
% 0.20/0.51  thf(t41_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( k2_tarski @ A @ B ) =
% 0.20/0.51       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (![X23 : $i, X24 : $i]:
% 0.20/0.51         ((k2_tarski @ X23 @ X24)
% 0.20/0.51           = (k2_xboole_0 @ (k1_tarski @ X23) @ (k1_tarski @ X24)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.20/0.51         <= (((r2_hidden @ sk_A @ sk_C)) & ((r2_hidden @ sk_B @ sk_C)))),
% 0.20/0.51      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      ((~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.20/0.51         <= (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.20/0.51      inference('split', [status(esa)], ['17'])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)) | 
% 0.20/0.51       ~ ((r2_hidden @ sk_A @ sk_C)) | ~ ((r2_hidden @ sk_B @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)) | 
% 0.20/0.51       ((r2_hidden @ sk_A @ sk_C))),
% 0.20/0.51      inference('split', [status(esa)], ['9'])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.51          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.51      inference('sup+', [status(thm)], ['2', '4'])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.51         (((X12) != (X11)) | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.20/0.51         ~ (zip_tseitin_0 @ X11 @ X13 @ X14 @ X11)),
% 0.20/0.51      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['35', '37'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.20/0.51           | (r2_hidden @ X0 @ sk_C)))
% 0.20/0.51         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '14'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (((r2_hidden @ sk_A @ sk_C))
% 0.20/0.51         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 0.20/0.51      inference('split', [status(esa)], ['17'])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)) | 
% 0.20/0.51       ((r2_hidden @ sk_A @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.51  thf('43', plain, ($false),
% 0.20/0.51      inference('sat_resolution*', [status(thm)],
% 0.20/0.51                ['1', '19', '20', '33', '34', '42'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
