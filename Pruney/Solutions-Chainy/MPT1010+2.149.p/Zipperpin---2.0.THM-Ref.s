%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mX3gb1nDO0

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:34 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   51 (  64 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  339 ( 570 expanded)
%              Number of equality atoms :   29 (  43 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t65_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( k1_funct_1 @ D @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ D @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('2',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ( X42 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X43 @ X40 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k1_tarski @ sk_B_1 ) )
      | ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ sk_C_1 ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( X10 = X7 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('9',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D_1 @ sk_C_1 )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ( k1_funct_1 @ sk_D_1 @ sk_C_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k1_tarski @ sk_B_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X8 != X7 )
      | ( r2_hidden @ X8 @ X9 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X7: $i] :
      ( r2_hidden @ X7 @ ( k1_tarski @ X7 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    r2_hidden @ sk_B_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['12','14'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('16',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('17',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('18',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('21',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['27'])).

thf('29',plain,(
    $false ),
    inference('sup-',[status(thm)],['15','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mX3gb1nDO0
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:46:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.52  % Solved by: fo/fo7.sh
% 0.19/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.52  % done 89 iterations in 0.069s
% 0.19/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.52  % SZS output start Refutation
% 0.19/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.52  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.19/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.52  thf(t65_funct_2, conjecture,
% 0.19/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.52     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.19/0.52         ( m1_subset_1 @
% 0.19/0.52           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.19/0.52       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.19/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.52        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.19/0.52            ( m1_subset_1 @
% 0.19/0.52              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.19/0.52          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.19/0.52    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.19/0.52  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('1', plain,
% 0.19/0.52      ((m1_subset_1 @ sk_D_1 @ 
% 0.19/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B_1))))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf(t7_funct_2, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.52     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.19/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.52       ( ( r2_hidden @ C @ A ) =>
% 0.19/0.52         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.19/0.52           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.19/0.52  thf('2', plain,
% 0.19/0.52      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.19/0.52         (~ (r2_hidden @ X40 @ X41)
% 0.19/0.52          | ((X42) = (k1_xboole_0))
% 0.19/0.52          | ~ (v1_funct_1 @ X43)
% 0.19/0.52          | ~ (v1_funct_2 @ X43 @ X41 @ X42)
% 0.19/0.52          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 0.19/0.52          | (r2_hidden @ (k1_funct_1 @ X43 @ X40) @ X42))),
% 0.19/0.52      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.19/0.52  thf('3', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_tarski @ sk_B_1))
% 0.19/0.52          | ~ (v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.19/0.52          | ~ (v1_funct_1 @ sk_D_1)
% 0.19/0.52          | ((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.19/0.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.19/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.52  thf('4', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ (k1_tarski @ sk_B_1))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('5', plain, ((v1_funct_1 @ sk_D_1)),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('6', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k1_tarski @ sk_B_1))
% 0.19/0.52          | ((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.19/0.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.19/0.52      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.19/0.52  thf('7', plain,
% 0.19/0.52      ((((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.19/0.52        | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ sk_C_1) @ (k1_tarski @ sk_B_1)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['0', '6'])).
% 0.19/0.52  thf(d1_tarski, axiom,
% 0.19/0.52    (![A:$i,B:$i]:
% 0.19/0.52     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.19/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.19/0.52  thf('8', plain,
% 0.19/0.52      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.19/0.52         (~ (r2_hidden @ X10 @ X9)
% 0.19/0.52          | ((X10) = (X7))
% 0.19/0.52          | ((X9) != (k1_tarski @ X7)))),
% 0.19/0.52      inference('cnf', [status(esa)], [d1_tarski])).
% 0.19/0.52  thf('9', plain,
% 0.19/0.52      (![X7 : $i, X10 : $i]:
% 0.19/0.52         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 0.19/0.52      inference('simplify', [status(thm)], ['8'])).
% 0.19/0.52  thf('10', plain,
% 0.19/0.52      ((((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.19/0.52        | ((k1_funct_1 @ sk_D_1 @ sk_C_1) = (sk_B_1)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['7', '9'])).
% 0.19/0.52  thf('11', plain, (((k1_funct_1 @ sk_D_1 @ sk_C_1) != (sk_B_1))),
% 0.19/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.52  thf('12', plain, (((k1_tarski @ sk_B_1) = (k1_xboole_0))),
% 0.19/0.52      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.19/0.52  thf('13', plain,
% 0.19/0.52      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.52         (((X8) != (X7)) | (r2_hidden @ X8 @ X9) | ((X9) != (k1_tarski @ X7)))),
% 0.19/0.52      inference('cnf', [status(esa)], [d1_tarski])).
% 0.19/0.52  thf('14', plain, (![X7 : $i]: (r2_hidden @ X7 @ (k1_tarski @ X7))),
% 0.19/0.52      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.52  thf('15', plain, ((r2_hidden @ sk_B_1 @ k1_xboole_0)),
% 0.19/0.52      inference('sup+', [status(thm)], ['12', '14'])).
% 0.19/0.52  thf(t7_xboole_0, axiom,
% 0.19/0.52    (![A:$i]:
% 0.19/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.52          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.19/0.52  thf('16', plain,
% 0.19/0.52      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.19/0.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.19/0.52  thf(d5_xboole_0, axiom,
% 0.19/0.52    (![A:$i,B:$i,C:$i]:
% 0.19/0.52     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.19/0.52       ( ![D:$i]:
% 0.19/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.52           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.19/0.52  thf('17', plain,
% 0.19/0.52      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.52         (~ (r2_hidden @ X4 @ X3)
% 0.19/0.52          | (r2_hidden @ X4 @ X1)
% 0.19/0.52          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.19/0.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.19/0.52  thf('18', plain,
% 0.19/0.52      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.19/0.52         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.19/0.52      inference('simplify', [status(thm)], ['17'])).
% 0.19/0.52  thf('19', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.19/0.52          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.19/0.52      inference('sup-', [status(thm)], ['16', '18'])).
% 0.19/0.52  thf('20', plain,
% 0.19/0.52      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.19/0.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.19/0.52  thf('21', plain,
% 0.19/0.52      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.52         (~ (r2_hidden @ X4 @ X3)
% 0.19/0.52          | ~ (r2_hidden @ X4 @ X2)
% 0.19/0.52          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.19/0.52      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.19/0.52  thf('22', plain,
% 0.19/0.52      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.19/0.52         (~ (r2_hidden @ X4 @ X2)
% 0.19/0.52          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.19/0.52      inference('simplify', [status(thm)], ['21'])).
% 0.19/0.52  thf('23', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.19/0.52          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.19/0.52      inference('sup-', [status(thm)], ['20', '22'])).
% 0.19/0.52  thf('24', plain,
% 0.19/0.52      (![X0 : $i]:
% 0.19/0.52         (((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 0.19/0.52          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.19/0.52      inference('sup-', [status(thm)], ['19', '23'])).
% 0.19/0.52  thf('25', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.19/0.52      inference('simplify', [status(thm)], ['24'])).
% 0.19/0.52  thf('26', plain,
% 0.19/0.52      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.19/0.52         (~ (r2_hidden @ X4 @ X2)
% 0.19/0.52          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.19/0.52      inference('simplify', [status(thm)], ['21'])).
% 0.19/0.52  thf('27', plain,
% 0.19/0.52      (![X0 : $i, X1 : $i]:
% 0.19/0.52         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.19/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.52  thf('28', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.52      inference('condensation', [status(thm)], ['27'])).
% 0.19/0.52  thf('29', plain, ($false), inference('sup-', [status(thm)], ['15', '28'])).
% 0.19/0.52  
% 0.19/0.52  % SZS output end Refutation
% 0.19/0.52  
% 0.19/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
