%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CZz2viGM62

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:35 EST 2020

% Result     : Theorem 0.33s
% Output     : Refutation 0.33s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 102 expanded)
%              Number of leaves         :   19 (  39 expanded)
%              Depth                    :   17
%              Number of atoms          :  468 ( 766 expanded)
%              Number of equality atoms :   38 (  65 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('1',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(d8_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( C
                  = ( k5_relat_1 @ A @ B ) )
              <=> ! [D: $i,E: $i] :
                    ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
                  <=> ? [F: $i] :
                        ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B )
                        & ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X9 @ X7 @ X8 ) @ ( sk_E @ X9 @ X7 @ X8 ) ) @ X9 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X9 @ X7 @ X8 ) @ ( sk_E @ X9 @ X7 @ X8 ) ) @ X7 )
      | ( X9
        = ( k5_relat_1 @ X8 @ X7 ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
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

thf('4',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('6',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('7',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) @ ( sk_E @ k1_xboole_0 @ X0 @ X1 ) ) @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('10',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) @ ( sk_E @ k1_xboole_0 @ X0 @ X1 ) ) @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','13'])).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t62_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
            = k1_xboole_0 )
          & ( ( k5_relat_1 @ A @ k1_xboole_0 )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_relat_1])).

thf('17',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('20',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('21',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X9 @ X7 @ X8 ) @ ( sk_E @ X9 @ X7 @ X8 ) ) @ X9 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X9 @ X7 @ X8 ) @ ( sk_F @ X9 @ X7 @ X8 ) ) @ X8 )
      | ( X9
        = ( k5_relat_1 @ X8 @ X7 ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_relat_1])).

thf('22',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ ( sk_F @ k1_xboole_0 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X0 @ X1 ) @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) ) @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X0 @ X1 ) @ ( sk_F @ k1_xboole_0 @ X0 @ X1 ) ) @ X1 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','28'])).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('33',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('38',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['36','37'])).

thf('39',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['18','38'])).

thf('40',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    $false ),
    inference(simplify,[status(thm)],['42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CZz2viGM62
% 0.13/0.37  % Computer   : n015.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 14:41:23 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.33/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.33/0.52  % Solved by: fo/fo7.sh
% 0.33/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.33/0.52  % done 32 iterations in 0.038s
% 0.33/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.33/0.52  % SZS output start Refutation
% 0.33/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.33/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.33/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.33/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.33/0.52  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.33/0.52  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.33/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.33/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.33/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.33/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.33/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.33/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.33/0.52  thf(cc1_relat_1, axiom,
% 0.33/0.52    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.33/0.52  thf('0', plain, (![X6 : $i]: ((v1_relat_1 @ X6) | ~ (v1_xboole_0 @ X6))),
% 0.33/0.52      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.33/0.52  thf('1', plain, (![X6 : $i]: ((v1_relat_1 @ X6) | ~ (v1_xboole_0 @ X6))),
% 0.33/0.52      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.33/0.52  thf(d8_relat_1, axiom,
% 0.33/0.52    (![A:$i]:
% 0.33/0.52     ( ( v1_relat_1 @ A ) =>
% 0.33/0.52       ( ![B:$i]:
% 0.33/0.52         ( ( v1_relat_1 @ B ) =>
% 0.33/0.52           ( ![C:$i]:
% 0.33/0.52             ( ( v1_relat_1 @ C ) =>
% 0.33/0.52               ( ( ( C ) = ( k5_relat_1 @ A @ B ) ) <=>
% 0.33/0.52                 ( ![D:$i,E:$i]:
% 0.33/0.52                   ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.33/0.52                     ( ?[F:$i]:
% 0.33/0.52                       ( ( r2_hidden @ ( k4_tarski @ F @ E ) @ B ) & 
% 0.33/0.52                         ( r2_hidden @ ( k4_tarski @ D @ F ) @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.33/0.52  thf('2', plain,
% 0.33/0.52      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.33/0.52         (~ (v1_relat_1 @ X7)
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k4_tarski @ (sk_D @ X9 @ X7 @ X8) @ (sk_E @ X9 @ X7 @ X8)) @ X9)
% 0.33/0.52          | (r2_hidden @ 
% 0.33/0.52             (k4_tarski @ (sk_F @ X9 @ X7 @ X8) @ (sk_E @ X9 @ X7 @ X8)) @ X7)
% 0.33/0.52          | ((X9) = (k5_relat_1 @ X8 @ X7))
% 0.33/0.53          | ~ (v1_relat_1 @ X9)
% 0.33/0.53          | ~ (v1_relat_1 @ X8))),
% 0.33/0.53      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.33/0.53  thf(t2_boole, axiom,
% 0.33/0.53    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.33/0.53  thf('3', plain,
% 0.33/0.53      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.33/0.53      inference('cnf', [status(esa)], [t2_boole])).
% 0.33/0.53  thf(t4_xboole_0, axiom,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.33/0.53            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.33/0.53       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.33/0.53            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.33/0.53  thf('4', plain,
% 0.33/0.53      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.33/0.53         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.33/0.53          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.33/0.53      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.33/0.53  thf('5', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]:
% 0.33/0.53         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.33/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.33/0.53  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.33/0.53  thf('6', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.33/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.33/0.53  thf('7', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.33/0.53      inference('demod', [status(thm)], ['5', '6'])).
% 0.33/0.53  thf('8', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]:
% 0.33/0.53         (~ (v1_relat_1 @ X0)
% 0.33/0.53          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.33/0.53          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 0.33/0.53          | (r2_hidden @ 
% 0.33/0.53             (k4_tarski @ (sk_F @ k1_xboole_0 @ X1 @ X0) @ 
% 0.33/0.53              (sk_E @ k1_xboole_0 @ X1 @ X0)) @ 
% 0.33/0.53             X1)
% 0.33/0.53          | ~ (v1_relat_1 @ X1))),
% 0.33/0.53      inference('sup-', [status(thm)], ['2', '7'])).
% 0.33/0.53  thf('9', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]:
% 0.33/0.53         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.33/0.53          | ~ (v1_relat_1 @ X0)
% 0.33/0.53          | (r2_hidden @ 
% 0.33/0.53             (k4_tarski @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ 
% 0.33/0.53              (sk_E @ k1_xboole_0 @ X0 @ X1)) @ 
% 0.33/0.53             X0)
% 0.33/0.53          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X0))
% 0.33/0.53          | ~ (v1_relat_1 @ X1))),
% 0.33/0.53      inference('sup-', [status(thm)], ['1', '8'])).
% 0.33/0.53  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.33/0.53  thf('10', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.33/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.33/0.53  thf('11', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]:
% 0.33/0.53         (~ (v1_relat_1 @ X0)
% 0.33/0.53          | (r2_hidden @ 
% 0.33/0.53             (k4_tarski @ (sk_F @ k1_xboole_0 @ X0 @ X1) @ 
% 0.33/0.53              (sk_E @ k1_xboole_0 @ X0 @ X1)) @ 
% 0.33/0.53             X0)
% 0.33/0.53          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X0))
% 0.33/0.53          | ~ (v1_relat_1 @ X1))),
% 0.33/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.33/0.53  thf('12', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.33/0.53      inference('demod', [status(thm)], ['5', '6'])).
% 0.33/0.53  thf('13', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         (~ (v1_relat_1 @ X0)
% 0.33/0.53          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.33/0.53          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.33/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.33/0.53  thf('14', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.33/0.53          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.33/0.53          | ~ (v1_relat_1 @ X0))),
% 0.33/0.53      inference('sup-', [status(thm)], ['0', '13'])).
% 0.33/0.53  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.33/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.33/0.53  thf('16', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.33/0.53          | ~ (v1_relat_1 @ X0))),
% 0.33/0.53      inference('demod', [status(thm)], ['14', '15'])).
% 0.33/0.53  thf(t62_relat_1, conjecture,
% 0.33/0.53    (![A:$i]:
% 0.33/0.53     ( ( v1_relat_1 @ A ) =>
% 0.33/0.53       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.33/0.53         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.33/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.33/0.53    (~( ![A:$i]:
% 0.33/0.53        ( ( v1_relat_1 @ A ) =>
% 0.33/0.53          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.33/0.53            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.33/0.53    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.33/0.53  thf('17', plain,
% 0.33/0.53      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.33/0.53        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('18', plain,
% 0.33/0.53      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.33/0.53         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.33/0.53      inference('split', [status(esa)], ['17'])).
% 0.33/0.53  thf('19', plain, (![X6 : $i]: ((v1_relat_1 @ X6) | ~ (v1_xboole_0 @ X6))),
% 0.33/0.53      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.33/0.53  thf('20', plain, (![X6 : $i]: ((v1_relat_1 @ X6) | ~ (v1_xboole_0 @ X6))),
% 0.33/0.53      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.33/0.53  thf('21', plain,
% 0.33/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.33/0.53         (~ (v1_relat_1 @ X7)
% 0.33/0.53          | (r2_hidden @ 
% 0.33/0.53             (k4_tarski @ (sk_D @ X9 @ X7 @ X8) @ (sk_E @ X9 @ X7 @ X8)) @ X9)
% 0.33/0.53          | (r2_hidden @ 
% 0.33/0.53             (k4_tarski @ (sk_D @ X9 @ X7 @ X8) @ (sk_F @ X9 @ X7 @ X8)) @ X8)
% 0.33/0.53          | ((X9) = (k5_relat_1 @ X8 @ X7))
% 0.33/0.53          | ~ (v1_relat_1 @ X9)
% 0.33/0.53          | ~ (v1_relat_1 @ X8))),
% 0.33/0.53      inference('cnf', [status(esa)], [d8_relat_1])).
% 0.33/0.53  thf('22', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.33/0.53      inference('demod', [status(thm)], ['5', '6'])).
% 0.33/0.53  thf('23', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]:
% 0.33/0.53         (~ (v1_relat_1 @ X0)
% 0.33/0.53          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.33/0.53          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 0.33/0.53          | (r2_hidden @ 
% 0.33/0.53             (k4_tarski @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ 
% 0.33/0.53              (sk_F @ k1_xboole_0 @ X1 @ X0)) @ 
% 0.33/0.53             X0)
% 0.33/0.53          | ~ (v1_relat_1 @ X1))),
% 0.33/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.33/0.53  thf('24', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]:
% 0.33/0.53         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.33/0.53          | ~ (v1_relat_1 @ X0)
% 0.33/0.53          | (r2_hidden @ 
% 0.33/0.53             (k4_tarski @ (sk_D @ k1_xboole_0 @ X0 @ X1) @ 
% 0.33/0.53              (sk_F @ k1_xboole_0 @ X0 @ X1)) @ 
% 0.33/0.53             X1)
% 0.33/0.53          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X0))
% 0.33/0.53          | ~ (v1_relat_1 @ X1))),
% 0.33/0.53      inference('sup-', [status(thm)], ['20', '23'])).
% 0.33/0.53  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.33/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.33/0.53  thf('26', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]:
% 0.33/0.53         (~ (v1_relat_1 @ X0)
% 0.33/0.53          | (r2_hidden @ 
% 0.33/0.53             (k4_tarski @ (sk_D @ k1_xboole_0 @ X0 @ X1) @ 
% 0.33/0.53              (sk_F @ k1_xboole_0 @ X0 @ X1)) @ 
% 0.33/0.53             X1)
% 0.33/0.53          | ((k1_xboole_0) = (k5_relat_1 @ X1 @ X0))
% 0.33/0.53          | ~ (v1_relat_1 @ X1))),
% 0.33/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.33/0.53  thf('27', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.33/0.53      inference('demod', [status(thm)], ['5', '6'])).
% 0.33/0.53  thf('28', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         (~ (v1_relat_1 @ k1_xboole_0)
% 0.33/0.53          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.33/0.53          | ~ (v1_relat_1 @ X0))),
% 0.33/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.33/0.53  thf('29', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.33/0.53          | ~ (v1_relat_1 @ X0)
% 0.33/0.53          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.33/0.53      inference('sup-', [status(thm)], ['19', '28'])).
% 0.33/0.53  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.33/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.33/0.53  thf('31', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         (~ (v1_relat_1 @ X0)
% 0.33/0.53          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.33/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.33/0.53  thf('32', plain,
% 0.33/0.53      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.33/0.53         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.33/0.53      inference('split', [status(esa)], ['17'])).
% 0.33/0.53  thf('33', plain,
% 0.33/0.53      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A)))
% 0.33/0.53         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.33/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.33/0.53  thf('34', plain, ((v1_relat_1 @ sk_A)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('35', plain,
% 0.33/0.53      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.33/0.53         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.33/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.33/0.53  thf('36', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.33/0.53      inference('simplify', [status(thm)], ['35'])).
% 0.33/0.53  thf('37', plain,
% 0.33/0.53      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.33/0.53       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.33/0.53      inference('split', [status(esa)], ['17'])).
% 0.33/0.53  thf('38', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.33/0.53      inference('sat_resolution*', [status(thm)], ['36', '37'])).
% 0.33/0.53  thf('39', plain, (((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.33/0.53      inference('simpl_trail', [status(thm)], ['18', '38'])).
% 0.33/0.53  thf('40', plain,
% 0.33/0.53      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.33/0.53      inference('sup-', [status(thm)], ['16', '39'])).
% 0.33/0.53  thf('41', plain, ((v1_relat_1 @ sk_A)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('42', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.33/0.53      inference('demod', [status(thm)], ['40', '41'])).
% 0.33/0.53  thf('43', plain, ($false), inference('simplify', [status(thm)], ['42'])).
% 0.33/0.53  
% 0.33/0.53  % SZS output end Refutation
% 0.33/0.53  
% 0.33/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
