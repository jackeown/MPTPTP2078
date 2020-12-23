%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QDvhpuZoCH

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:36 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 133 expanded)
%              Number of leaves         :   16 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  402 (1636 expanded)
%              Number of equality atoms :   74 ( 374 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('3',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r1_tarski @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('9',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X26
        = ( k1_tarski @ X25 ) )
      | ( X26 = k1_xboole_0 )
      | ~ ( r1_tarski @ X26 @ ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('10',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('14',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    r1_tarski @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X26
        = ( k1_tarski @ X25 ) )
      | ( X26 = k1_xboole_0 )
      | ~ ( r1_tarski @ X26 @ ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('20',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['11'])).

thf('26',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['13','15','27'])).

thf('29',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['12','28'])).

thf('30',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('31',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('33',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['12','28'])).

thf('39',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['21'])).

thf('41',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['39','40'])).

thf('42',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['30','41'])).

thf('43',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['10','29','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QDvhpuZoCH
% 0.17/0.37  % Computer   : n004.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 10:22:09 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.37  % Python version: Python 3.6.8
% 0.17/0.37  % Running in FO mode
% 0.23/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.46  % Solved by: fo/fo7.sh
% 0.23/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.46  % done 88 iterations in 0.022s
% 0.23/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.46  % SZS output start Refutation
% 0.23/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.46  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.23/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.46  thf(t43_zfmisc_1, conjecture,
% 0.23/0.46    (![A:$i,B:$i,C:$i]:
% 0.23/0.46     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.23/0.46          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.23/0.46          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.23/0.46          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.23/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.46        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.23/0.46             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.23/0.46             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.23/0.46             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.23/0.46    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.23/0.46  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.23/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.46  thf(d3_tarski, axiom,
% 0.23/0.46    (![A:$i,B:$i]:
% 0.23/0.46     ( ( r1_tarski @ A @ B ) <=>
% 0.23/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.23/0.46  thf('1', plain,
% 0.23/0.46      (![X1 : $i, X3 : $i]:
% 0.23/0.46         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.23/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.46  thf(d3_xboole_0, axiom,
% 0.23/0.46    (![A:$i,B:$i,C:$i]:
% 0.23/0.46     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.23/0.46       ( ![D:$i]:
% 0.23/0.46         ( ( r2_hidden @ D @ C ) <=>
% 0.23/0.46           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.23/0.46  thf('2', plain,
% 0.23/0.46      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.23/0.46         (~ (r2_hidden @ X4 @ X5)
% 0.23/0.46          | (r2_hidden @ X4 @ X6)
% 0.23/0.46          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 0.23/0.46      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.23/0.46  thf('3', plain,
% 0.23/0.46      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.23/0.46         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X5))),
% 0.23/0.46      inference('simplify', [status(thm)], ['2'])).
% 0.23/0.46  thf('4', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.46         ((r1_tarski @ X0 @ X1)
% 0.23/0.46          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_xboole_0 @ X2 @ X0)))),
% 0.23/0.46      inference('sup-', [status(thm)], ['1', '3'])).
% 0.23/0.46  thf('5', plain,
% 0.23/0.46      (![X1 : $i, X3 : $i]:
% 0.23/0.46         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.23/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.46  thf('6', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i]:
% 0.23/0.46         ((r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 0.23/0.46          | (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.23/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.46  thf('7', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.23/0.46      inference('simplify', [status(thm)], ['6'])).
% 0.23/0.46  thf('8', plain, ((r1_tarski @ sk_C_1 @ (k1_tarski @ sk_A))),
% 0.23/0.46      inference('sup+', [status(thm)], ['0', '7'])).
% 0.23/0.46  thf(l3_zfmisc_1, axiom,
% 0.23/0.46    (![A:$i,B:$i]:
% 0.23/0.46     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.23/0.46       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.23/0.46  thf('9', plain,
% 0.23/0.46      (![X25 : $i, X26 : $i]:
% 0.23/0.46         (((X26) = (k1_tarski @ X25))
% 0.23/0.46          | ((X26) = (k1_xboole_0))
% 0.23/0.46          | ~ (r1_tarski @ X26 @ (k1_tarski @ X25)))),
% 0.23/0.46      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.23/0.46  thf('10', plain,
% 0.23/0.46      ((((sk_C_1) = (k1_xboole_0)) | ((sk_C_1) = (k1_tarski @ sk_A)))),
% 0.23/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.46  thf('11', plain,
% 0.23/0.46      ((((sk_B) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.23/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.46  thf('12', plain,
% 0.23/0.46      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 0.23/0.46         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 0.23/0.46      inference('split', [status(esa)], ['11'])).
% 0.23/0.46  thf('13', plain,
% 0.23/0.46      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.23/0.46      inference('split', [status(esa)], ['11'])).
% 0.23/0.46  thf('14', plain,
% 0.23/0.46      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.23/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.46  thf('15', plain,
% 0.23/0.46      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.23/0.46      inference('split', [status(esa)], ['14'])).
% 0.23/0.46  thf('16', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.23/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.46  thf(t7_xboole_1, axiom,
% 0.23/0.46    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.23/0.46  thf('17', plain,
% 0.23/0.46      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.23/0.46      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.23/0.46  thf('18', plain, ((r1_tarski @ sk_B @ (k1_tarski @ sk_A))),
% 0.23/0.46      inference('sup+', [status(thm)], ['16', '17'])).
% 0.23/0.46  thf('19', plain,
% 0.23/0.46      (![X25 : $i, X26 : $i]:
% 0.23/0.46         (((X26) = (k1_tarski @ X25))
% 0.23/0.46          | ((X26) = (k1_xboole_0))
% 0.23/0.46          | ~ (r1_tarski @ X26 @ (k1_tarski @ X25)))),
% 0.23/0.46      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.23/0.46  thf('20', plain,
% 0.23/0.46      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k1_tarski @ sk_A)))),
% 0.23/0.46      inference('sup-', [status(thm)], ['18', '19'])).
% 0.23/0.46  thf('21', plain,
% 0.23/0.46      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 0.23/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.46  thf('22', plain,
% 0.23/0.46      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.23/0.46      inference('split', [status(esa)], ['21'])).
% 0.23/0.46  thf('23', plain,
% 0.23/0.46      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.23/0.46         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.23/0.46      inference('sup-', [status(thm)], ['20', '22'])).
% 0.23/0.46  thf('24', plain,
% 0.23/0.46      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.23/0.46      inference('simplify', [status(thm)], ['23'])).
% 0.23/0.46  thf('25', plain,
% 0.23/0.46      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.23/0.46      inference('split', [status(esa)], ['11'])).
% 0.23/0.46  thf('26', plain,
% 0.23/0.46      ((((sk_B) != (sk_B)))
% 0.23/0.46         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.23/0.46      inference('sup-', [status(thm)], ['24', '25'])).
% 0.23/0.46  thf('27', plain,
% 0.23/0.46      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.23/0.46      inference('simplify', [status(thm)], ['26'])).
% 0.23/0.46  thf('28', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 0.23/0.46      inference('sat_resolution*', [status(thm)], ['13', '15', '27'])).
% 0.23/0.46  thf('29', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.23/0.46      inference('simpl_trail', [status(thm)], ['12', '28'])).
% 0.23/0.46  thf('30', plain,
% 0.23/0.46      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.23/0.46      inference('split', [status(esa)], ['21'])).
% 0.23/0.46  thf('31', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 0.23/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.46  thf('32', plain,
% 0.23/0.46      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.23/0.46      inference('simplify', [status(thm)], ['23'])).
% 0.23/0.46  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.23/0.46  thf('33', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.23/0.46      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.23/0.46  thf(t12_xboole_1, axiom,
% 0.23/0.46    (![A:$i,B:$i]:
% 0.23/0.46     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.23/0.46  thf('34', plain,
% 0.23/0.46      (![X10 : $i, X11 : $i]:
% 0.23/0.46         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 0.23/0.46      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.23/0.46  thf('35', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.23/0.46      inference('sup-', [status(thm)], ['33', '34'])).
% 0.23/0.46  thf('36', plain,
% 0.23/0.46      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 0.23/0.46         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.23/0.46      inference('sup+', [status(thm)], ['32', '35'])).
% 0.23/0.46  thf('37', plain,
% 0.23/0.46      ((((k1_tarski @ sk_A) = (sk_C_1))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.23/0.46      inference('sup+', [status(thm)], ['31', '36'])).
% 0.23/0.46  thf('38', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.23/0.46      inference('simpl_trail', [status(thm)], ['12', '28'])).
% 0.23/0.46  thf('39', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 0.23/0.46      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.23/0.46  thf('40', plain,
% 0.23/0.46      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.23/0.46      inference('split', [status(esa)], ['21'])).
% 0.23/0.46  thf('41', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 0.23/0.46      inference('sat_resolution*', [status(thm)], ['39', '40'])).
% 0.23/0.46  thf('42', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.23/0.46      inference('simpl_trail', [status(thm)], ['30', '41'])).
% 0.23/0.46  thf('43', plain, ($false),
% 0.23/0.46      inference('simplify_reflect-', [status(thm)], ['10', '29', '42'])).
% 0.23/0.46  
% 0.23/0.46  % SZS output end Refutation
% 0.23/0.46  
% 0.23/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
