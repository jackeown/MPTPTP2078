%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BzoP3JHJb9

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:36 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   30 (  38 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :  150 ( 278 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t176_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v5_relat_1 @ C @ A )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) )
       => ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v5_relat_1 @ C @ A )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) )
         => ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t176_funct_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k1_funct_1 @ sk_C @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    r2_hidden @ sk_B_1 @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X7 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X7 @ X6 ) @ X8 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v5_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v5_relat_1 @ sk_C @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_C @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C @ sk_B_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['1','7'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( m1_subset_1 @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_C @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    $false ),
    inference(demod,[status(thm)],['0','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BzoP3JHJb9
% 0.14/0.38  % Computer   : n009.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 10:35:41 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.39  % Running in FO mode
% 0.23/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.51  % Solved by: fo/fo7.sh
% 0.23/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.51  % done 22 iterations in 0.014s
% 0.23/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.51  % SZS output start Refutation
% 0.23/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.23/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.23/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.23/0.51  thf(t176_funct_1, conjecture,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & ( v1_funct_1 @ C ) ) =>
% 0.23/0.51       ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) =>
% 0.23/0.51         ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ))).
% 0.23/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.51        ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & ( v1_funct_1 @ C ) ) =>
% 0.23/0.51          ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) =>
% 0.23/0.51            ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ) )),
% 0.23/0.51    inference('cnf.neg', [status(esa)], [t176_funct_1])).
% 0.23/0.51  thf('0', plain, (~ (m1_subset_1 @ (k1_funct_1 @ sk_C @ sk_B_1) @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('1', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('2', plain, ((r2_hidden @ sk_B_1 @ (k1_relat_1 @ sk_C))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(t172_funct_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.23/0.51       ( ![C:$i]:
% 0.23/0.51         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.23/0.51           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 0.23/0.51  thf('3', plain,
% 0.23/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.23/0.51         (~ (r2_hidden @ X6 @ (k1_relat_1 @ X7))
% 0.23/0.51          | (r2_hidden @ (k1_funct_1 @ X7 @ X6) @ X8)
% 0.23/0.51          | ~ (v1_funct_1 @ X7)
% 0.23/0.51          | ~ (v5_relat_1 @ X7 @ X8)
% 0.23/0.51          | ~ (v1_relat_1 @ X7))),
% 0.23/0.51      inference('cnf', [status(esa)], [t172_funct_1])).
% 0.23/0.51  thf('4', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (~ (v1_relat_1 @ sk_C)
% 0.23/0.51          | ~ (v5_relat_1 @ sk_C @ X0)
% 0.23/0.51          | ~ (v1_funct_1 @ sk_C)
% 0.23/0.51          | (r2_hidden @ (k1_funct_1 @ sk_C @ sk_B_1) @ X0))),
% 0.23/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.23/0.51  thf('5', plain, ((v1_relat_1 @ sk_C)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('7', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (~ (v5_relat_1 @ sk_C @ X0)
% 0.23/0.51          | (r2_hidden @ (k1_funct_1 @ sk_C @ sk_B_1) @ X0))),
% 0.23/0.51      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.23/0.51  thf('8', plain, ((r2_hidden @ (k1_funct_1 @ sk_C @ sk_B_1) @ sk_A)),
% 0.23/0.51      inference('sup-', [status(thm)], ['1', '7'])).
% 0.23/0.51  thf(d2_subset_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( ( v1_xboole_0 @ A ) =>
% 0.23/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.23/0.51       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.23/0.51  thf('9', plain,
% 0.23/0.51      (![X3 : $i, X4 : $i]:
% 0.23/0.51         (~ (r2_hidden @ X3 @ X4)
% 0.23/0.51          | (m1_subset_1 @ X3 @ X4)
% 0.23/0.51          | (v1_xboole_0 @ X4))),
% 0.23/0.51      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.23/0.51  thf(d1_xboole_0, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.23/0.51  thf('10', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.23/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.23/0.51  thf('11', plain,
% 0.23/0.51      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 0.23/0.51      inference('clc', [status(thm)], ['9', '10'])).
% 0.23/0.51  thf('12', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_C @ sk_B_1) @ sk_A)),
% 0.23/0.51      inference('sup-', [status(thm)], ['8', '11'])).
% 0.23/0.51  thf('13', plain, ($false), inference('demod', [status(thm)], ['0', '12'])).
% 0.23/0.51  
% 0.23/0.51  % SZS output end Refutation
% 0.23/0.51  
% 0.23/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
