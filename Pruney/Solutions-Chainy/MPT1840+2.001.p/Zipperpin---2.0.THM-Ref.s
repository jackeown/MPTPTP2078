%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JDyRT0gciH

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   22 (  30 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :   87 ( 191 expanded)
%              Number of equality atoms :    3 (  11 expanded)
%              Maximal formula depth    :   10 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( v7_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf(t4_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( ( ( u1_struct_0 @ A )
                = ( u1_struct_0 @ B ) )
              & ( v7_struct_0 @ A ) )
           => ( v7_struct_0 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( l1_struct_0 @ B )
           => ( ( ( ( u1_struct_0 @ A )
                  = ( u1_struct_0 @ B ) )
                & ( v7_struct_0 @ A ) )
             => ( v7_struct_0 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_tex_2])).

thf('1',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc6_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v7_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_struct_0])).

thf('3',plain,
    ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v7_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v7_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v7_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v7_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    v7_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    $false ),
    inference(demod,[status(thm)],['8','9','10'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JDyRT0gciH
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:25:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 7 iterations in 0.007s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.47  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(fc7_struct_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.47       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (![X1 : $i]:
% 0.21/0.47         ((v1_zfmisc_1 @ (u1_struct_0 @ X1))
% 0.21/0.47          | ~ (l1_struct_0 @ X1)
% 0.21/0.47          | ~ (v7_struct_0 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.21/0.47  thf(t4_tex_2, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_struct_0 @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( l1_struct_0 @ B ) =>
% 0.21/0.47           ( ( ( ( u1_struct_0 @ A ) = ( u1_struct_0 @ B ) ) & 
% 0.21/0.47               ( v7_struct_0 @ A ) ) =>
% 0.21/0.47             ( v7_struct_0 @ B ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( l1_struct_0 @ A ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( l1_struct_0 @ B ) =>
% 0.21/0.47              ( ( ( ( u1_struct_0 @ A ) = ( u1_struct_0 @ B ) ) & 
% 0.21/0.47                  ( v7_struct_0 @ A ) ) =>
% 0.21/0.47                ( v7_struct_0 @ B ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t4_tex_2])).
% 0.21/0.47  thf('1', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(fc6_struct_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v7_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.47       ( ~( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (v1_zfmisc_1 @ (u1_struct_0 @ X0))
% 0.21/0.47          | ~ (l1_struct_0 @ X0)
% 0.21/0.47          | (v7_struct_0 @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc6_struct_0])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      ((~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.21/0.47        | (v7_struct_0 @ sk_B)
% 0.21/0.47        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('4', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      ((~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A)) | (v7_struct_0 @ sk_B))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.47  thf('6', plain, (~ (v7_struct_0 @ sk_B)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('7', plain, (~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('clc', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('8', plain, ((~ (v7_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '7'])).
% 0.21/0.47  thf('9', plain, ((v7_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('10', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('11', plain, ($false),
% 0.21/0.47      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
