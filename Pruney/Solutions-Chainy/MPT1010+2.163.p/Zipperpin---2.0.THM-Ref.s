%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q6PcXEI562

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  61 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  284 ( 534 expanded)
%              Number of equality atoms :   22 (  38 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ( k1_funct_1 @ sk_D @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( X17 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_2 @ X18 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X18 @ X15 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_C_1 ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( X4 = X1 )
      | ( X3
       != ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('10',plain,(
    ! [X1: $i,X4: $i] :
      ( ( X4 = X1 )
      | ~ ( r2_hidden @ X4 @ ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D @ sk_C_1 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ( k1_funct_1 @ sk_D @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k1_tarski @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( X2 != X1 )
      | ( r2_hidden @ X2 @ X3 )
      | ( X3
       != ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X1: $i] :
      ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    r2_hidden @ sk_B @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['13','15'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B @ X0 ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X1: $i,X4: $i] :
      ( ( X4 = X1 )
      | ~ ( r2_hidden @ X4 @ ( k1_tarski @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('24',plain,(
    ! [X0: $i] : ( sk_B = X0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    sk_B != sk_B ),
    inference(demod,[status(thm)],['0','24'])).

thf('26',plain,(
    $false ),
    inference(simplify,[status(thm)],['25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q6PcXEI562
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:56:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 43 iterations in 0.035s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(t65_funct_2, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.21/0.51         ( m1_subset_1 @
% 0.21/0.51           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.21/0.51       ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) ) & 
% 0.21/0.51            ( m1_subset_1 @
% 0.21/0.51              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) ) =>
% 0.21/0.51          ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ D @ C ) = ( B ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t65_funct_2])).
% 0.21/0.51  thf('0', plain, (((k1_funct_1 @ sk_D @ sk_C_1) != (sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D @ 
% 0.21/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t7_funct_2, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.51       ( ( r2_hidden @ C @ A ) =>
% 0.21/0.51         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.51           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X15 @ X16)
% 0.21/0.51          | ((X17) = (k1_xboole_0))
% 0.21/0.51          | ~ (v1_funct_1 @ X18)
% 0.21/0.51          | ~ (v1_funct_2 @ X18 @ X16 @ X17)
% 0.21/0.51          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.21/0.51          | (r2_hidden @ (k1_funct_1 @ X18 @ X15) @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [t7_funct_2])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.21/0.51          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))
% 0.21/0.51          | ~ (v1_funct_1 @ sk_D)
% 0.21/0.51          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.51          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k1_tarski @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k1_tarski @ sk_B))
% 0.21/0.51          | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.51          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.51        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_C_1) @ (k1_tarski @ sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '7'])).
% 0.21/0.51  thf(d1_tarski, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X4 @ X3) | ((X4) = (X1)) | ((X3) != (k1_tarski @ X1)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X1 : $i, X4 : $i]:
% 0.21/0.51         (((X4) = (X1)) | ~ (r2_hidden @ X4 @ (k1_tarski @ X1)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      ((((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.21/0.51        | ((k1_funct_1 @ sk_D @ sk_C_1) = (sk_B)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['8', '10'])).
% 0.21/0.51  thf('12', plain, (((k1_funct_1 @ sk_D @ sk_C_1) != (sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('13', plain, (((k1_tarski @ sk_B) = (k1_xboole_0))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.51         (((X2) != (X1)) | (r2_hidden @ X2 @ X3) | ((X3) != (k1_tarski @ X1)))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.51  thf('15', plain, (![X1 : $i]: (r2_hidden @ X1 @ (k1_tarski @ X1))),
% 0.21/0.51      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.51  thf('16', plain, ((r2_hidden @ sk_B @ k1_xboole_0)),
% 0.21/0.51      inference('sup+', [status(thm)], ['13', '15'])).
% 0.21/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.51  thf('17', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.51  thf(t3_subset, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X12 : $i, X14 : $i]:
% 0.21/0.51         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf(l3_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X9 @ X10)
% 0.21/0.51          | (r2_hidden @ X9 @ X11)
% 0.21/0.51          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.21/0.51      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('22', plain, (![X0 : $i]: (r2_hidden @ sk_B @ X0)),
% 0.21/0.51      inference('sup-', [status(thm)], ['16', '21'])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X1 : $i, X4 : $i]:
% 0.21/0.51         (((X4) = (X1)) | ~ (r2_hidden @ X4 @ (k1_tarski @ X1)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.51  thf('24', plain, (![X0 : $i]: ((sk_B) = (X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.51  thf('25', plain, (((sk_B) != (sk_B))),
% 0.21/0.51      inference('demod', [status(thm)], ['0', '24'])).
% 0.21/0.51  thf('26', plain, ($false), inference('simplify', [status(thm)], ['25'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
