%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gcqRYlgHKM

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:25 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 123 expanded)
%              Number of leaves         :   20 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  385 (1336 expanded)
%              Number of equality atoms :    6 (  47 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_relat_1_type,type,(
    v2_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v5_funct_1_type,type,(
    v5_funct_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t173_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v5_funct_1 @ A @ B )
              & ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) ) )
           => ( v2_relat_1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ( ( ( v5_funct_1 @ A @ B )
                & ( ( k1_relat_1 @ A )
                  = ( k1_relat_1 @ B ) ) )
             => ( v2_relat_1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t173_funct_1])).

thf('0',plain,(
    v5_funct_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_relat_1 @ sk_A )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d15_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_relat_1 @ A )
      <=> ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
              & ( v1_xboole_0 @ ( k1_funct_1 @ A @ B ) ) ) ) ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( ( r2_hidden @ ( sk_B @ X6 ) @ ( k1_relat_1 @ X6 ) )
      | ( v2_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d15_funct_1])).

thf('3',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) )
    | ( v2_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v2_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ),
    inference(clc,[status(thm)],['6','7'])).

thf(d20_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( v5_funct_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
               => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v5_funct_1 @ X8 @ X9 )
      | ( r2_hidden @ ( k1_funct_1 @ X8 @ X10 ) @ ( k1_funct_1 @ X9 @ X10 ) )
      | ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d20_funct_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ ( k1_funct_1 @ X0 @ ( sk_B @ sk_B_1 ) ) )
      | ~ ( v5_funct_1 @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ ( k1_funct_1 @ X0 @ ( sk_B @ sk_B_1 ) ) )
      | ~ ( v5_funct_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X6: $i] :
      ( ( v1_xboole_0 @ ( k1_funct_1 @ X6 @ ( sk_B @ X6 ) ) )
      | ( v2_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d15_funct_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_relat_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

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

thf('22',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X1 )
      | ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) @ X0 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( v2_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('25',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('26',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('27',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('28',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X1 )
      | ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_relat_1 @ sk_B_1 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['24','32','33','34'])).

thf('36',plain,(
    ~ ( v2_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( k1_funct_1 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ X0 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    $false ),
    inference('sup-',[status(thm)],['17','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gcqRYlgHKM
% 0.15/0.37  % Computer   : n021.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 17:12:04 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.23/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.46  % Solved by: fo/fo7.sh
% 0.23/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.46  % done 72 iterations in 0.023s
% 0.23/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.46  % SZS output start Refutation
% 0.23/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.46  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.23/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.46  thf(v2_relat_1_type, type, v2_relat_1: $i > $o).
% 0.23/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.46  thf(sk_B_type, type, sk_B: $i > $i).
% 0.23/0.46  thf(v5_funct_1_type, type, v5_funct_1: $i > $i > $o).
% 0.23/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.46  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.23/0.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.46  thf(t173_funct_1, conjecture,
% 0.23/0.46    (![A:$i]:
% 0.23/0.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.46       ( ![B:$i]:
% 0.23/0.46         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.23/0.46           ( ( ( v5_funct_1 @ A @ B ) & 
% 0.23/0.46               ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) ) =>
% 0.23/0.46             ( v2_relat_1 @ B ) ) ) ) ))).
% 0.23/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.46    (~( ![A:$i]:
% 0.23/0.46        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.46          ( ![B:$i]:
% 0.23/0.46            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.23/0.46              ( ( ( v5_funct_1 @ A @ B ) & 
% 0.23/0.46                  ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) ) =>
% 0.23/0.46                ( v2_relat_1 @ B ) ) ) ) ) )),
% 0.23/0.46    inference('cnf.neg', [status(esa)], [t173_funct_1])).
% 0.23/0.46  thf('0', plain, ((v5_funct_1 @ sk_A @ sk_B_1)),
% 0.23/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.46  thf('1', plain, (((k1_relat_1 @ sk_A) = (k1_relat_1 @ sk_B_1))),
% 0.23/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.46  thf(d15_funct_1, axiom,
% 0.23/0.46    (![A:$i]:
% 0.23/0.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.46       ( ( v2_relat_1 @ A ) <=>
% 0.23/0.46         ( ![B:$i]:
% 0.23/0.46           ( ~( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.23/0.46                ( v1_xboole_0 @ ( k1_funct_1 @ A @ B ) ) ) ) ) ) ))).
% 0.23/0.46  thf('2', plain,
% 0.23/0.46      (![X6 : $i]:
% 0.23/0.46         ((r2_hidden @ (sk_B @ X6) @ (k1_relat_1 @ X6))
% 0.23/0.46          | (v2_relat_1 @ X6)
% 0.23/0.46          | ~ (v1_funct_1 @ X6)
% 0.23/0.46          | ~ (v1_relat_1 @ X6))),
% 0.23/0.46      inference('cnf', [status(esa)], [d15_funct_1])).
% 0.23/0.46  thf('3', plain,
% 0.23/0.46      (((r2_hidden @ (sk_B @ sk_B_1) @ (k1_relat_1 @ sk_A))
% 0.23/0.46        | ~ (v1_relat_1 @ sk_B_1)
% 0.23/0.46        | ~ (v1_funct_1 @ sk_B_1)
% 0.23/0.46        | (v2_relat_1 @ sk_B_1))),
% 0.23/0.46      inference('sup+', [status(thm)], ['1', '2'])).
% 0.23/0.46  thf('4', plain, ((v1_relat_1 @ sk_B_1)),
% 0.23/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.46  thf('5', plain, ((v1_funct_1 @ sk_B_1)),
% 0.23/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.46  thf('6', plain,
% 0.23/0.46      (((r2_hidden @ (sk_B @ sk_B_1) @ (k1_relat_1 @ sk_A))
% 0.23/0.46        | (v2_relat_1 @ sk_B_1))),
% 0.23/0.46      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.23/0.46  thf('7', plain, (~ (v2_relat_1 @ sk_B_1)),
% 0.23/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.46  thf('8', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (k1_relat_1 @ sk_A))),
% 0.23/0.46      inference('clc', [status(thm)], ['6', '7'])).
% 0.23/0.46  thf(d20_funct_1, axiom,
% 0.23/0.46    (![A:$i]:
% 0.23/0.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.46       ( ![B:$i]:
% 0.23/0.46         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.23/0.46           ( ( v5_funct_1 @ B @ A ) <=>
% 0.23/0.46             ( ![C:$i]:
% 0.23/0.46               ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.23/0.46                 ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ ( k1_funct_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.23/0.46  thf('9', plain,
% 0.23/0.46      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.23/0.46         (~ (v1_relat_1 @ X8)
% 0.23/0.46          | ~ (v1_funct_1 @ X8)
% 0.23/0.46          | ~ (v5_funct_1 @ X8 @ X9)
% 0.23/0.46          | (r2_hidden @ (k1_funct_1 @ X8 @ X10) @ (k1_funct_1 @ X9 @ X10))
% 0.23/0.46          | ~ (r2_hidden @ X10 @ (k1_relat_1 @ X8))
% 0.23/0.46          | ~ (v1_funct_1 @ X9)
% 0.23/0.46          | ~ (v1_relat_1 @ X9))),
% 0.23/0.46      inference('cnf', [status(esa)], [d20_funct_1])).
% 0.23/0.46  thf('10', plain,
% 0.23/0.46      (![X0 : $i]:
% 0.23/0.46         (~ (v1_relat_1 @ X0)
% 0.23/0.46          | ~ (v1_funct_1 @ X0)
% 0.23/0.46          | (r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ 
% 0.23/0.46             (k1_funct_1 @ X0 @ (sk_B @ sk_B_1)))
% 0.23/0.46          | ~ (v5_funct_1 @ sk_A @ X0)
% 0.23/0.46          | ~ (v1_funct_1 @ sk_A)
% 0.23/0.46          | ~ (v1_relat_1 @ sk_A))),
% 0.23/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.46  thf('11', plain, ((v1_funct_1 @ sk_A)),
% 0.23/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.46  thf('12', plain, ((v1_relat_1 @ sk_A)),
% 0.23/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.46  thf('13', plain,
% 0.23/0.46      (![X0 : $i]:
% 0.23/0.46         (~ (v1_relat_1 @ X0)
% 0.23/0.46          | ~ (v1_funct_1 @ X0)
% 0.23/0.46          | (r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ 
% 0.23/0.46             (k1_funct_1 @ X0 @ (sk_B @ sk_B_1)))
% 0.23/0.46          | ~ (v5_funct_1 @ sk_A @ X0))),
% 0.23/0.46      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.23/0.46  thf('14', plain,
% 0.23/0.46      (((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ 
% 0.23/0.46         (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.23/0.46        | ~ (v1_funct_1 @ sk_B_1)
% 0.23/0.46        | ~ (v1_relat_1 @ sk_B_1))),
% 0.23/0.46      inference('sup-', [status(thm)], ['0', '13'])).
% 0.23/0.46  thf('15', plain, ((v1_funct_1 @ sk_B_1)),
% 0.23/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.46  thf('16', plain, ((v1_relat_1 @ sk_B_1)),
% 0.23/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.46  thf('17', plain,
% 0.23/0.46      ((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ 
% 0.23/0.46        (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))),
% 0.23/0.46      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.23/0.46  thf('18', plain,
% 0.23/0.46      (![X6 : $i]:
% 0.23/0.46         ((v1_xboole_0 @ (k1_funct_1 @ X6 @ (sk_B @ X6)))
% 0.23/0.46          | (v2_relat_1 @ X6)
% 0.23/0.46          | ~ (v1_funct_1 @ X6)
% 0.23/0.46          | ~ (v1_relat_1 @ X6))),
% 0.23/0.46      inference('cnf', [status(esa)], [d15_funct_1])).
% 0.23/0.46  thf(l13_xboole_0, axiom,
% 0.23/0.46    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.23/0.46  thf('19', plain,
% 0.23/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.23/0.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.23/0.46  thf('20', plain,
% 0.23/0.46      (![X0 : $i]:
% 0.23/0.46         (~ (v1_relat_1 @ X0)
% 0.23/0.46          | ~ (v1_funct_1 @ X0)
% 0.23/0.46          | (v2_relat_1 @ X0)
% 0.23/0.46          | ((k1_funct_1 @ X0 @ (sk_B @ X0)) = (k1_xboole_0)))),
% 0.23/0.46      inference('sup-', [status(thm)], ['18', '19'])).
% 0.23/0.46  thf('21', plain,
% 0.23/0.46      ((r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ 
% 0.23/0.46        (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))),
% 0.23/0.46      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.23/0.46  thf(t3_xboole_0, axiom,
% 0.23/0.46    (![A:$i,B:$i]:
% 0.23/0.46     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.23/0.46            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.23/0.46       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.23/0.46            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.23/0.46  thf('22', plain,
% 0.23/0.46      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.23/0.46         (~ (r2_hidden @ X3 @ X1)
% 0.23/0.46          | ~ (r2_hidden @ X3 @ X4)
% 0.23/0.46          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.23/0.46      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.23/0.46  thf('23', plain,
% 0.23/0.46      (![X0 : $i]:
% 0.23/0.46         (~ (r1_xboole_0 @ (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)) @ X0)
% 0.23/0.46          | ~ (r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ X0))),
% 0.23/0.46      inference('sup-', [status(thm)], ['21', '22'])).
% 0.23/0.46  thf('24', plain,
% 0.23/0.46      (![X0 : $i]:
% 0.23/0.46         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.23/0.46          | (v2_relat_1 @ sk_B_1)
% 0.23/0.46          | ~ (v1_funct_1 @ sk_B_1)
% 0.23/0.46          | ~ (v1_relat_1 @ sk_B_1)
% 0.23/0.46          | ~ (r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ X0))),
% 0.23/0.46      inference('sup-', [status(thm)], ['20', '23'])).
% 0.23/0.46  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.23/0.46  thf('25', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.23/0.46      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.23/0.46  thf('26', plain,
% 0.23/0.46      (![X1 : $i, X2 : $i]:
% 0.23/0.46         ((r1_xboole_0 @ X1 @ X2) | (r2_hidden @ (sk_C @ X2 @ X1) @ X1))),
% 0.23/0.46      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.23/0.46  thf('27', plain,
% 0.23/0.46      (![X1 : $i, X2 : $i]:
% 0.23/0.46         ((r1_xboole_0 @ X1 @ X2) | (r2_hidden @ (sk_C @ X2 @ X1) @ X1))),
% 0.23/0.46      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.23/0.46  thf('28', plain,
% 0.23/0.46      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.23/0.46         (~ (r2_hidden @ X3 @ X1)
% 0.23/0.46          | ~ (r2_hidden @ X3 @ X4)
% 0.23/0.46          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.23/0.46      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.23/0.46  thf('29', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.46         ((r1_xboole_0 @ X0 @ X1)
% 0.23/0.46          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.23/0.46          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.23/0.46      inference('sup-', [status(thm)], ['27', '28'])).
% 0.23/0.46  thf('30', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i]:
% 0.23/0.46         ((r1_xboole_0 @ X0 @ X1)
% 0.23/0.46          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.23/0.46          | (r1_xboole_0 @ X0 @ X1))),
% 0.23/0.46      inference('sup-', [status(thm)], ['26', '29'])).
% 0.23/0.46  thf('31', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i]:
% 0.23/0.46         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.23/0.46      inference('simplify', [status(thm)], ['30'])).
% 0.23/0.46  thf('32', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.23/0.46      inference('sup-', [status(thm)], ['25', '31'])).
% 0.23/0.46  thf('33', plain, ((v1_funct_1 @ sk_B_1)),
% 0.23/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.46  thf('34', plain, ((v1_relat_1 @ sk_B_1)),
% 0.23/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.46  thf('35', plain,
% 0.23/0.46      (![X0 : $i]:
% 0.23/0.46         ((v2_relat_1 @ sk_B_1)
% 0.23/0.46          | ~ (r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ X0))),
% 0.23/0.46      inference('demod', [status(thm)], ['24', '32', '33', '34'])).
% 0.23/0.46  thf('36', plain, (~ (v2_relat_1 @ sk_B_1)),
% 0.23/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.46  thf('37', plain,
% 0.23/0.46      (![X0 : $i]: ~ (r2_hidden @ (k1_funct_1 @ sk_A @ (sk_B @ sk_B_1)) @ X0)),
% 0.23/0.46      inference('clc', [status(thm)], ['35', '36'])).
% 0.23/0.46  thf('38', plain, ($false), inference('sup-', [status(thm)], ['17', '37'])).
% 0.23/0.46  
% 0.23/0.46  % SZS output end Refutation
% 0.23/0.46  
% 0.23/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
