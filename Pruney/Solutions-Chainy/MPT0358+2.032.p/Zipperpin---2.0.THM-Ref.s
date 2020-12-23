%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UZVFVUPGfx

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 118 expanded)
%              Number of leaves         :   19 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  348 ( 957 expanded)
%              Number of equality atoms :   34 (  89 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t38_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
        <=> ( B
            = ( k1_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X61: $i,X62: $i] :
      ( ( ( k3_subset_1 @ X61 @ X62 )
        = ( k4_xboole_0 @ X61 @ X62 ) )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ X61 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('4',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('9',plain,(
    ! [X21: $i] :
      ( ( r1_xboole_0 @ X21 @ X21 )
      | ( X21 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('10',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['9'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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

thf('13',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X60: $i] :
      ( ( k1_subset_1 @ X60 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('19',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('20',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('22',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('24',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('27',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['8','25','26'])).

thf('28',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['6','27'])).

thf('29',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['4','28'])).

thf('30',plain,(
    ! [X60: $i] :
      ( ( k1_subset_1 @ X60 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('31',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('32',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    sk_B
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['8','25'])).

thf('34',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['32','33'])).

thf('35',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['29','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UZVFVUPGfx
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:35:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 286 iterations in 0.058s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.22/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.52  thf(t38_subset_1, conjecture,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.22/0.52         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i]:
% 0.22/0.52        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.22/0.52            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.22/0.52  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(d5_subset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X61 : $i, X62 : $i]:
% 0.22/0.52         (((k3_subset_1 @ X61 @ X62) = (k4_xboole_0 @ X61 @ X62))
% 0.22/0.52          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ X61)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.52  thf(t38_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.22/0.52       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X13 : $i, X14 : $i]:
% 0.22/0.52         (((X13) = (k1_xboole_0))
% 0.22/0.52          | ~ (r1_tarski @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.22/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      ((((sk_B) = (k1_subset_1 @ sk_A))
% 0.22/0.52        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.22/0.52         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.22/0.52      inference('split', [status(esa)], ['5'])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      ((((sk_B) != (k1_subset_1 @ sk_A))
% 0.22/0.52        | ~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (~ (((sk_B) = (k1_subset_1 @ sk_A))) | 
% 0.22/0.52       ~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('split', [status(esa)], ['7'])).
% 0.22/0.52  thf(t66_xboole_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.22/0.52       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      (![X21 : $i]: ((r1_xboole_0 @ X21 @ X21) | ((X21) != (k1_xboole_0)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.22/0.52  thf('10', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.22/0.52      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.52  thf(d3_tarski, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X3 : $i, X5 : $i]:
% 0.22/0.52         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (![X3 : $i, X5 : $i]:
% 0.22/0.52         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.52  thf(t3_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.22/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.52            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X9 @ X7)
% 0.22/0.52          | ~ (r2_hidden @ X9 @ X10)
% 0.22/0.52          | ~ (r1_xboole_0 @ X7 @ X10))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         ((r1_tarski @ X0 @ X1)
% 0.22/0.52          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.22/0.52          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.22/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((r1_tarski @ X0 @ X1)
% 0.22/0.52          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.22/0.52          | (r1_tarski @ X0 @ X1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['11', '14'])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (r1_tarski @ X0 @ X1))),
% 0.22/0.52      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.52  thf('17', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.52      inference('sup-', [status(thm)], ['10', '16'])).
% 0.22/0.52  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.52  thf('18', plain, (![X60 : $i]: ((k1_subset_1 @ X60) = (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      ((((sk_B) = (k1_subset_1 @ sk_A))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.22/0.52      inference('split', [status(esa)], ['5'])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.22/0.52      inference('sup+', [status(thm)], ['18', '19'])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.22/0.52         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.22/0.52      inference('split', [status(esa)], ['7'])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.22/0.52         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.22/0.52             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.22/0.52      inference('sup+', [status(thm)], ['18', '19'])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.22/0.52         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.22/0.52             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.22/0.52      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.22/0.52       ~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['17', '24'])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.22/0.52       (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.22/0.52      inference('split', [status(esa)], ['5'])).
% 0.22/0.52  thf('27', plain, (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['8', '25', '26'])).
% 0.22/0.52  thf('28', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['6', '27'])).
% 0.22/0.52  thf('29', plain, (((sk_B) = (k1_xboole_0))),
% 0.22/0.52      inference('demod', [status(thm)], ['4', '28'])).
% 0.22/0.52  thf('30', plain, (![X60 : $i]: ((k1_subset_1 @ X60) = (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      ((((sk_B) != (k1_subset_1 @ sk_A)))
% 0.22/0.52         <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.22/0.52      inference('split', [status(esa)], ['7'])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.52  thf('33', plain, (~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['8', '25'])).
% 0.22/0.52  thf('34', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['32', '33'])).
% 0.22/0.52  thf('35', plain, ($false),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['29', '34'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
