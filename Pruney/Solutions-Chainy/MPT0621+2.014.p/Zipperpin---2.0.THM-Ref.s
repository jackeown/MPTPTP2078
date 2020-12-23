%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6KXmyUwA9x

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 117 expanded)
%              Number of leaves         :   21 (  46 expanded)
%              Depth                    :   17
%              Number of atoms          :  414 (1047 expanded)
%              Number of equality atoms :   53 ( 132 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(np__1_type,type,(
    np__1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(s3_funct_1__e2_24__funct_1,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ! [D: $i] :
          ( ( r2_hidden @ D @ A )
         => ( ( k1_funct_1 @ C @ D )
            = B ) )
      & ( ( k1_relat_1 @ C )
        = A )
      & ( v1_funct_1 @ C )
      & ( v1_relat_1 @ C ) ) )).

thf('0',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_relat_1 @ ( sk_C_1 @ X16 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf(s3_funct_1__e7_25__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = np__1 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('1',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf(t16_funct_1,conjecture,(
    ! [A: $i] :
      ( ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ( ( ( ( k1_relat_1 @ B )
                    = A )
                  & ( ( k1_relat_1 @ C )
                    = A ) )
               => ( B = C ) ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_relat_1 @ C )
                  & ( v1_funct_1 @ C ) )
               => ( ( ( ( k1_relat_1 @ B )
                      = A )
                    & ( ( k1_relat_1 @ C )
                      = A ) )
                 => ( B = C ) ) ) )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t16_funct_1])).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ( X22 = X21 )
      | ( ( k1_relat_1 @ X21 )
       != sk_A )
      | ( ( k1_relat_1 @ X22 )
       != sk_A )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_B_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X19: $i] :
      ( v1_funct_1 @ ( sk_B_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('5',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( sk_B_1 @ sk_A ) )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ( ( sk_C_1 @ X1 @ X0 )
        = ( sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( sk_C_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_funct_1 @ ( sk_C_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ( ( sk_C_1 @ X1 @ X0 )
        = ( sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X1: $i] :
      ( ( sk_C_1 @ X1 @ sk_A )
      = ( sk_B_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k1_funct_1 @ ( sk_B_1 @ X19 ) @ X20 )
        = np__1 )
      | ~ ( r2_hidden @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_funct_1 @ ( sk_B_1 @ X0 ) @ ( sk_B @ X0 ) )
        = np__1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X0 @ sk_A ) @ ( sk_B @ sk_A ) )
        = np__1 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X16 @ X17 ) @ X18 )
        = X16 )
      | ~ ( r2_hidden @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_B @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( np__1 = X0 )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( np__1 = X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( np__1 = X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['26'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('29',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14
        = ( k1_relat_1 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X14 @ X11 ) @ ( sk_D_1 @ X14 @ X11 ) ) @ X11 )
      | ( r2_hidden @ ( sk_C @ X14 @ X11 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0
        = ( k1_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0
        = ( k1_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['37'])).

thf('39',plain,(
    k1_xboole_0 = sk_A ),
    inference('sup-',[status(thm)],['27','38'])).

thf('40',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6KXmyUwA9x
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:06:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 110 iterations in 0.109s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.56  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.56  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.56  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.56  thf(np__1_type, type, np__1: $i).
% 0.21/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.56  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ?[C:$i]:
% 0.21/0.56       ( ( ![D:$i]:
% 0.21/0.56           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.21/0.56         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.56         ( v1_relat_1 @ C ) ) ))).
% 0.21/0.56  thf('0', plain,
% 0.21/0.56      (![X16 : $i, X17 : $i]: ((k1_relat_1 @ (sk_C_1 @ X16 @ X17)) = (X17))),
% 0.21/0.56      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.21/0.56  thf(s3_funct_1__e7_25__funct_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ?[B:$i]:
% 0.21/0.56       ( ( ![C:$i]:
% 0.21/0.56           ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( np__1 ) ) ) ) & 
% 0.21/0.56         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.21/0.56         ( v1_relat_1 @ B ) ) ))).
% 0.21/0.56  thf('1', plain, (![X19 : $i]: ((k1_relat_1 @ (sk_B_1 @ X19)) = (X19))),
% 0.21/0.56      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.21/0.56  thf(t16_funct_1, conjecture,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ![B:$i]:
% 0.21/0.56         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.56               ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.56                   ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.21/0.56                 ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.21/0.56       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i]:
% 0.21/0.56        ( ( ![B:$i]:
% 0.21/0.56            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.56              ( ![C:$i]:
% 0.21/0.56                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.56                  ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.56                      ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.21/0.56                    ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.21/0.56          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t16_funct_1])).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      (![X21 : $i, X22 : $i]:
% 0.21/0.56         (~ (v1_relat_1 @ X21)
% 0.21/0.56          | ~ (v1_funct_1 @ X21)
% 0.21/0.56          | ((X22) = (X21))
% 0.21/0.56          | ((k1_relat_1 @ X21) != (sk_A))
% 0.21/0.56          | ((k1_relat_1 @ X22) != (sk_A))
% 0.21/0.56          | ~ (v1_funct_1 @ X22)
% 0.21/0.56          | ~ (v1_relat_1 @ X22))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((X0) != (sk_A))
% 0.21/0.56          | ~ (v1_relat_1 @ X1)
% 0.21/0.56          | ~ (v1_funct_1 @ X1)
% 0.21/0.56          | ((k1_relat_1 @ X1) != (sk_A))
% 0.21/0.56          | ((X1) = (sk_B_1 @ X0))
% 0.21/0.56          | ~ (v1_funct_1 @ (sk_B_1 @ X0))
% 0.21/0.56          | ~ (v1_relat_1 @ (sk_B_1 @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf('4', plain, (![X19 : $i]: (v1_funct_1 @ (sk_B_1 @ X19))),
% 0.21/0.56      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.21/0.56  thf('5', plain, (![X19 : $i]: (v1_relat_1 @ (sk_B_1 @ X19))),
% 0.21/0.56      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((X0) != (sk_A))
% 0.21/0.56          | ~ (v1_relat_1 @ X1)
% 0.21/0.56          | ~ (v1_funct_1 @ X1)
% 0.21/0.56          | ((k1_relat_1 @ X1) != (sk_A))
% 0.21/0.56          | ((X1) = (sk_B_1 @ X0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (![X1 : $i]:
% 0.21/0.56         (((X1) = (sk_B_1 @ sk_A))
% 0.21/0.56          | ((k1_relat_1 @ X1) != (sk_A))
% 0.21/0.56          | ~ (v1_funct_1 @ X1)
% 0.21/0.56          | ~ (v1_relat_1 @ X1))),
% 0.21/0.56      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((X0) != (sk_A))
% 0.21/0.56          | ~ (v1_relat_1 @ (sk_C_1 @ X1 @ X0))
% 0.21/0.56          | ~ (v1_funct_1 @ (sk_C_1 @ X1 @ X0))
% 0.21/0.56          | ((sk_C_1 @ X1 @ X0) = (sk_B_1 @ sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['0', '7'])).
% 0.21/0.56  thf('9', plain, (![X16 : $i, X17 : $i]: (v1_relat_1 @ (sk_C_1 @ X16 @ X17))),
% 0.21/0.56      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.21/0.56  thf('10', plain,
% 0.21/0.56      (![X16 : $i, X17 : $i]: (v1_funct_1 @ (sk_C_1 @ X16 @ X17))),
% 0.21/0.56      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.21/0.56  thf('11', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((X0) != (sk_A)) | ((sk_C_1 @ X1 @ X0) = (sk_B_1 @ sk_A)))),
% 0.21/0.56      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.56  thf('12', plain, (![X1 : $i]: ((sk_C_1 @ X1 @ sk_A) = (sk_B_1 @ sk_A))),
% 0.21/0.56      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.56  thf(d1_xboole_0, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (![X19 : $i, X20 : $i]:
% 0.21/0.56         (((k1_funct_1 @ (sk_B_1 @ X19) @ X20) = (np__1))
% 0.21/0.56          | ~ (r2_hidden @ X20 @ X19))),
% 0.21/0.56      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v1_xboole_0 @ X0)
% 0.21/0.56          | ((k1_funct_1 @ (sk_B_1 @ X0) @ (sk_B @ X0)) = (np__1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k1_funct_1 @ (sk_C_1 @ X0 @ sk_A) @ (sk_B @ sk_A)) = (np__1))
% 0.21/0.56          | (v1_xboole_0 @ sk_A))),
% 0.21/0.56      inference('sup+', [status(thm)], ['12', '15'])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.56         (((k1_funct_1 @ (sk_C_1 @ X16 @ X17) @ X18) = (X16))
% 0.21/0.56          | ~ (r2_hidden @ X18 @ X17))),
% 0.21/0.56      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((v1_xboole_0 @ X0)
% 0.21/0.56          | ((k1_funct_1 @ (sk_C_1 @ X1 @ X0) @ (sk_B @ X0)) = (X1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((np__1) = (X0)) | (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_A))),
% 0.21/0.56      inference('sup+', [status(thm)], ['16', '19'])).
% 0.21/0.56  thf('21', plain, (![X0 : $i]: ((v1_xboole_0 @ sk_A) | ((np__1) = (X0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.56  thf('22', plain, (![X0 : $i]: ((v1_xboole_0 @ sk_A) | ((np__1) = (X0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((X0) = (X1)) | (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_A))),
% 0.21/0.56      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ sk_A) | ((X0) = (X1)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.56  thf('25', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (v1_xboole_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.56  thf('27', plain, ((v1_xboole_0 @ sk_A)),
% 0.21/0.56      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.56  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.56  thf(d4_relat_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.21/0.56       ( ![C:$i]:
% 0.21/0.56         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.56           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.21/0.56  thf('29', plain,
% 0.21/0.56      (![X11 : $i, X14 : $i]:
% 0.21/0.56         (((X14) = (k1_relat_1 @ X11))
% 0.21/0.56          | (r2_hidden @ 
% 0.21/0.56             (k4_tarski @ (sk_C @ X14 @ X11) @ (sk_D_1 @ X14 @ X11)) @ X11)
% 0.21/0.56          | (r2_hidden @ (sk_C @ X14 @ X11) @ X14))),
% 0.21/0.56      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.21/0.56          | ((X1) = (k1_relat_1 @ X0))
% 0.21/0.56          | ~ (v1_xboole_0 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.56  thf('33', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (v1_xboole_0 @ X1)
% 0.21/0.56          | ((X0) = (k1_relat_1 @ X1))
% 0.21/0.56          | ~ (v1_xboole_0 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (v1_xboole_0 @ X1)
% 0.21/0.56          | ((X0) = (k1_relat_1 @ X1))
% 0.21/0.56          | ~ (v1_xboole_0 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (((X1) = (X0))
% 0.21/0.56          | ~ (v1_xboole_0 @ X0)
% 0.21/0.56          | ~ (v1_xboole_0 @ X2)
% 0.21/0.56          | ~ (v1_xboole_0 @ X1)
% 0.21/0.56          | ~ (v1_xboole_0 @ X2))),
% 0.21/0.56      inference('sup+', [status(thm)], ['33', '34'])).
% 0.21/0.56  thf('36', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (v1_xboole_0 @ X1)
% 0.21/0.56          | ~ (v1_xboole_0 @ X2)
% 0.21/0.56          | ~ (v1_xboole_0 @ X0)
% 0.21/0.56          | ((X1) = (X0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.56  thf('37', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['28', '36'])).
% 0.21/0.56  thf('38', plain,
% 0.21/0.56      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.56      inference('condensation', [status(thm)], ['37'])).
% 0.21/0.56  thf('39', plain, (((k1_xboole_0) = (sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['27', '38'])).
% 0.21/0.56  thf('40', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('41', plain, ($false),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
