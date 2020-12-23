%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ot39w1d1Ay

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:51 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   32 (  42 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  138 ( 308 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(t8_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) )
              & ( v7_struct_0 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) )
                & ( v7_struct_0 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X1: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( v7_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('2',plain,(
    v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
              & ( v1_zfmisc_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ X3 )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ X3 @ X2 ) @ X3 )
      | ~ ( v1_zfmisc_1 @ X3 )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t6_tex_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v7_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    v7_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['0','14'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ot39w1d1Ay
% 0.12/0.32  % Computer   : n010.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 09:14:00 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running portfolio for 600 s
% 0.12/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.32  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.19/0.43  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.43  % Solved by: fo/fo7.sh
% 0.19/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.43  % done 10 iterations in 0.006s
% 0.19/0.43  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.43  % SZS output start Refutation
% 0.19/0.43  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.43  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.43  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.19/0.43  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.43  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.19/0.43  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.43  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.43  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.43  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.19/0.43  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.19/0.43  thf(t8_tex_2, conjecture,
% 0.19/0.43    (![A:$i]:
% 0.19/0.43     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.43       ( ![B:$i]:
% 0.19/0.43         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.43           ( ~( ( v1_subset_1 @
% 0.19/0.43                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.19/0.43                  ( u1_struct_0 @ A ) ) & 
% 0.19/0.43                ( v7_struct_0 @ A ) ) ) ) ) ))).
% 0.19/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.43    (~( ![A:$i]:
% 0.19/0.43        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.43          ( ![B:$i]:
% 0.19/0.43            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.43              ( ~( ( v1_subset_1 @
% 0.19/0.43                     ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.19/0.43                     ( u1_struct_0 @ A ) ) & 
% 0.19/0.43                   ( v7_struct_0 @ A ) ) ) ) ) ) )),
% 0.19/0.43    inference('cnf.neg', [status(esa)], [t8_tex_2])).
% 0.19/0.43  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf(fc7_struct_0, axiom,
% 0.19/0.43    (![A:$i]:
% 0.19/0.43     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.43       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.19/0.43  thf('1', plain,
% 0.19/0.43      (![X1 : $i]:
% 0.19/0.43         ((v1_zfmisc_1 @ (u1_struct_0 @ X1))
% 0.19/0.43          | ~ (l1_struct_0 @ X1)
% 0.19/0.43          | ~ (v7_struct_0 @ X1))),
% 0.19/0.43      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.19/0.43  thf('2', plain,
% 0.19/0.43      ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.43        (u1_struct_0 @ sk_A))),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf(t6_tex_2, axiom,
% 0.19/0.43    (![A:$i]:
% 0.19/0.43     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.43       ( ![B:$i]:
% 0.19/0.43         ( ( m1_subset_1 @ B @ A ) =>
% 0.19/0.43           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.19/0.43                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.19/0.43  thf('3', plain,
% 0.19/0.43      (![X2 : $i, X3 : $i]:
% 0.19/0.43         (~ (m1_subset_1 @ X2 @ X3)
% 0.19/0.43          | ~ (v1_subset_1 @ (k6_domain_1 @ X3 @ X2) @ X3)
% 0.19/0.43          | ~ (v1_zfmisc_1 @ X3)
% 0.19/0.43          | (v1_xboole_0 @ X3))),
% 0.19/0.43      inference('cnf', [status(esa)], [t6_tex_2])).
% 0.19/0.43  thf('4', plain,
% 0.19/0.43      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.43        | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.19/0.43        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.19/0.43      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.43  thf('5', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('6', plain,
% 0.19/0.43      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.43        | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.43      inference('demod', [status(thm)], ['4', '5'])).
% 0.19/0.43  thf('7', plain,
% 0.19/0.43      ((~ (v7_struct_0 @ sk_A)
% 0.19/0.43        | ~ (l1_struct_0 @ sk_A)
% 0.19/0.43        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.43      inference('sup-', [status(thm)], ['1', '6'])).
% 0.19/0.43  thf('8', plain, ((v7_struct_0 @ sk_A)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('9', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('10', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.19/0.43      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.19/0.43  thf(fc2_struct_0, axiom,
% 0.19/0.43    (![A:$i]:
% 0.19/0.43     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.43       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.19/0.43  thf('11', plain,
% 0.19/0.43      (![X0 : $i]:
% 0.19/0.43         (~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.19/0.43          | ~ (l1_struct_0 @ X0)
% 0.19/0.43          | (v2_struct_0 @ X0))),
% 0.19/0.43      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.19/0.43  thf('12', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.43      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.43  thf('13', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.43  thf('14', plain, ((v2_struct_0 @ sk_A)),
% 0.19/0.43      inference('demod', [status(thm)], ['12', '13'])).
% 0.19/0.43  thf('15', plain, ($false), inference('demod', [status(thm)], ['0', '14'])).
% 0.19/0.43  
% 0.19/0.43  % SZS output end Refutation
% 0.19/0.43  
% 0.19/0.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
