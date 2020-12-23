%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E72hMEAAxm

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 108 expanded)
%              Number of leaves         :   23 (  43 expanded)
%              Depth                    :   17
%              Number of atoms          :  474 ( 962 expanded)
%              Number of equality atoms :   73 ( 147 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t15_funct_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
        ? [C: $i] :
          ( ( ( k2_relat_1 @ C )
            = ( k1_tarski @ B ) )
          & ( ( k1_relat_1 @ C )
            = A )
          & ( v1_funct_1 @ C )
          & ( v1_relat_1 @ C ) ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_2 @ X14 @ X15 ) )
        = X15 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_funct_1 @ ( sk_C_2 @ X14 @ X15 ) )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( X9 = X6 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9 = X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_2 @ X14 @ X15 ) )
        = ( k1_tarski @ X14 ) )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(t18_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( ( A = k1_xboole_0 )
            & ( B != k1_xboole_0 ) )
        & ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ~ ( ( B
                  = ( k1_relat_1 @ C ) )
                & ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ~ ( ( A = k1_xboole_0 )
              & ( B != k1_xboole_0 ) )
          & ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ~ ( ( B
                    = ( k1_relat_1 @ C ) )
                  & ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_funct_1])).

thf('12',plain,(
    ! [X16: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ sk_A )
      | ( sk_B_2
       != ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ( sk_B_2
       != ( k1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( sk_B_2
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ ( sk_B @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_B @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf(s3_funct_1__e2_25__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = k1_xboole_0 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('18',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('19',plain,(
    ! [X11: $i] :
      ( ( ( k1_relat_1 @ X11 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X11 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( sk_B_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k2_relat_1 @ ( sk_B_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_relat_1 @ ( sk_B_1 @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X16: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ sk_A )
      | ( sk_B_2
       != ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ ( sk_B_1 @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( sk_B_1 @ k1_xboole_0 ) )
    | ( sk_B_2
     != ( k1_relat_1 @ ( sk_B_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('26',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('27',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('28',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( sk_B_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('29',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('30',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(demod,[status(thm)],['25','26','27','28','29'])).

thf('31',plain,
    ( ( sk_B_2 != sk_B_2 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','30'])).

thf('32',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('34',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['32','33'])).

thf('35',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['16','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( sk_B_2
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ ( sk_B @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_B @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['14','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_B @ sk_A ) @ X0 ) )
      | ( sk_B_2
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_B @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( sk_B_2
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_B @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_relat_1 @ ( sk_C_2 @ X14 @ X15 ) )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B_2
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_B @ sk_A ) @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( sk_B_2 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','40'])).

thf('42',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(demod,[status(thm)],['25','26','27','28','29'])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.E72hMEAAxm
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:07:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 58 iterations in 0.035s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.20/0.48  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.48  thf(t15_funct_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ?[C:$i]:
% 0.20/0.48           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.20/0.48             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.48             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i]:
% 0.20/0.48         (((k1_relat_1 @ (sk_C_2 @ X14 @ X15)) = (X15))
% 0.20/0.48          | ((X15) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i]:
% 0.20/0.48         ((v1_funct_1 @ (sk_C_2 @ X14 @ X15)) | ((X15) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.48  thf(t7_xboole_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.48          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.48  thf(d3_tarski, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X1 : $i, X3 : $i]:
% 0.20/0.48         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.48  thf(d1_tarski, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X9 @ X8) | ((X9) = (X6)) | ((X8) != (k1_tarski @ X6)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X6 : $i, X9 : $i]:
% 0.20/0.48         (((X9) = (X6)) | ~ (r2_hidden @ X9 @ (k1_tarski @ X6)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.20/0.48          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['3', '5'])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X1 : $i, X3 : $i]:
% 0.20/0.48         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.48          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.20/0.48          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.48      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '9'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i]:
% 0.20/0.48         (((k2_relat_1 @ (sk_C_2 @ X14 @ X15)) = (k1_tarski @ X14))
% 0.20/0.48          | ((X15) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.48  thf(t18_funct_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.48          ( ![C:$i]:
% 0.20/0.48            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.48              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.20/0.48                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i]:
% 0.20/0.48        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.48             ( ![C:$i]:
% 0.20/0.48               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.48                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.20/0.48                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X16 : $i]:
% 0.20/0.48         (~ (r1_tarski @ (k2_relat_1 @ X16) @ sk_A)
% 0.20/0.48          | ((sk_B_2) != (k1_relat_1 @ X16))
% 0.20/0.48          | ~ (v1_funct_1 @ X16)
% 0.20/0.48          | ~ (v1_relat_1 @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.20/0.48          | ((X1) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ (sk_C_2 @ X0 @ X1))
% 0.20/0.48          | ~ (v1_funct_1 @ (sk_C_2 @ X0 @ X1))
% 0.20/0.48          | ((sk_B_2) != (k1_relat_1 @ (sk_C_2 @ X0 @ X1))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((sk_A) = (k1_xboole_0))
% 0.20/0.48          | ((sk_B_2) != (k1_relat_1 @ (sk_C_2 @ (sk_B @ sk_A) @ X0)))
% 0.20/0.48          | ~ (v1_funct_1 @ (sk_C_2 @ (sk_B @ sk_A) @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_B @ sk_A) @ X0))
% 0.20/0.48          | ((X0) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['10', '13'])).
% 0.20/0.48  thf('15', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_2) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.20/0.48      inference('split', [status(esa)], ['15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.20/0.48      inference('split', [status(esa)], ['15'])).
% 0.20/0.48  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ?[B:$i]:
% 0.20/0.48       ( ( ![C:$i]:
% 0.20/0.48           ( ( r2_hidden @ C @ A ) =>
% 0.20/0.48             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.48         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.20/0.48         ( v1_relat_1 @ B ) ) ))).
% 0.20/0.48  thf('18', plain, (![X12 : $i]: ((k1_relat_1 @ (sk_B_1 @ X12)) = (X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.48  thf(t65_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.48         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X11 : $i]:
% 0.20/0.48         (((k1_relat_1 @ X11) != (k1_xboole_0))
% 0.20/0.48          | ((k2_relat_1 @ X11) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((X0) != (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ (sk_B_1 @ X0))
% 0.20/0.48          | ((k2_relat_1 @ (sk_B_1 @ X0)) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.48  thf('21', plain, (![X12 : $i]: (v1_relat_1 @ (sk_B_1 @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((X0) != (k1_xboole_0))
% 0.20/0.48          | ((k2_relat_1 @ (sk_B_1 @ X0)) = (k1_xboole_0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.48  thf('23', plain, (((k2_relat_1 @ (sk_B_1 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X16 : $i]:
% 0.20/0.48         (~ (r1_tarski @ (k2_relat_1 @ X16) @ sk_A)
% 0.20/0.48          | ((sk_B_2) != (k1_relat_1 @ X16))
% 0.20/0.48          | ~ (v1_funct_1 @ X16)
% 0.20/0.48          | ~ (v1_relat_1 @ X16))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.20/0.48        | ~ (v1_relat_1 @ (sk_B_1 @ k1_xboole_0))
% 0.20/0.48        | ~ (v1_funct_1 @ (sk_B_1 @ k1_xboole_0))
% 0.20/0.48        | ((sk_B_2) != (k1_relat_1 @ (sk_B_1 @ k1_xboole_0))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.48  thf('26', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.20/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.48  thf('27', plain, (![X12 : $i]: (v1_relat_1 @ (sk_B_1 @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.48  thf('28', plain, (![X12 : $i]: (v1_funct_1 @ (sk_B_1 @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.48  thf('29', plain, (![X12 : $i]: ((k1_relat_1 @ (sk_B_1 @ X12)) = (X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.48  thf('30', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['25', '26', '27', '28', '29'])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      ((((sk_B_2) != (sk_B_2))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '30'])).
% 0.20/0.48  thf('32', plain, (~ (((sk_B_2) = (k1_xboole_0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_2) = (k1_xboole_0)))),
% 0.20/0.48      inference('split', [status(esa)], ['15'])).
% 0.20/0.48  thf('34', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['32', '33'])).
% 0.20/0.48  thf('35', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['16', '34'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((sk_B_2) != (k1_relat_1 @ (sk_C_2 @ (sk_B @ sk_A) @ X0)))
% 0.20/0.48          | ~ (v1_funct_1 @ (sk_C_2 @ (sk_B @ sk_A) @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_B @ sk_A) @ X0))
% 0.20/0.48          | ((X0) = (k1_xboole_0)))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['14', '35'])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((X0) = (k1_xboole_0))
% 0.20/0.48          | ((X0) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_B @ sk_A) @ X0))
% 0.20/0.48          | ((sk_B_2) != (k1_relat_1 @ (sk_C_2 @ (sk_B @ sk_A) @ X0))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '36'])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((sk_B_2) != (k1_relat_1 @ (sk_C_2 @ (sk_B @ sk_A) @ X0)))
% 0.20/0.48          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_B @ sk_A) @ X0))
% 0.20/0.48          | ((X0) = (k1_xboole_0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i]:
% 0.20/0.48         ((v1_relat_1 @ (sk_C_2 @ X14 @ X15)) | ((X15) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((X0) = (k1_xboole_0))
% 0.20/0.48          | ((sk_B_2) != (k1_relat_1 @ (sk_C_2 @ (sk_B @ sk_A) @ X0))))),
% 0.20/0.49      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((sk_B_2) != (X0)) | ((X0) = (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '40'])).
% 0.20/0.49  thf('42', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.49  thf('43', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['25', '26', '27', '28', '29'])).
% 0.20/0.49  thf('44', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
