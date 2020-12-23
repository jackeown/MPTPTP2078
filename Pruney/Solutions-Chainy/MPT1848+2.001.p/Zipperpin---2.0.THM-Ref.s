%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MENxpY9KRz

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:55 EST 2020

% Result     : Theorem 0.33s
% Output     : Refutation 0.33s
% Verified   : 
% Statistics : Number of formulae       :   46 (  69 expanded)
%              Number of leaves         :   15 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :  301 ( 577 expanded)
%              Number of equality atoms :   10 (  28 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t15_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ~ ( ( ( u1_struct_0 @ B )
                = ( u1_struct_0 @ A ) )
              & ( v1_tex_2 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_pre_topc @ B @ A )
           => ~ ( ( ( u1_struct_0 @ B )
                  = ( u1_struct_0 @ A ) )
                & ( v1_tex_2 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_tex_2])).

thf('0',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('1',plain,(
    ! [X15: $i] :
      ( ( m1_pre_topc @ X15 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(l17_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[l17_tex_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_subset_1 @ X17 @ X16 )
      | ( X17 != X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('6',plain,(
    ! [X16: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( v1_subset_1 @ X16 @ X16 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('13',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                <=> ( v1_tex_2 @ B @ A ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( X22
       != ( u1_struct_0 @ X20 ) )
      | ~ ( v1_tex_2 @ X20 @ X21 )
      | ( v1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t13_tex_2])).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_tex_2 @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_tex_2 @ X0 @ sk_A )
      | ( v1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_tex_2 @ X0 @ sk_A )
      | ( v1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v1_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    v1_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['20','25','26','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['11','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MENxpY9KRz
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:31:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.33/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.33/0.53  % Solved by: fo/fo7.sh
% 0.33/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.33/0.53  % done 97 iterations in 0.065s
% 0.33/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.33/0.53  % SZS output start Refutation
% 0.33/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.33/0.53  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.33/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.33/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.33/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.33/0.53  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.33/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.33/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.33/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.33/0.53  thf(t15_tex_2, conjecture,
% 0.33/0.53    (![A:$i]:
% 0.33/0.53     ( ( l1_pre_topc @ A ) =>
% 0.33/0.53       ( ![B:$i]:
% 0.33/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.33/0.53           ( ~( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ A ) ) & 
% 0.33/0.53                ( v1_tex_2 @ B @ A ) ) ) ) ) ))).
% 0.33/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.33/0.53    (~( ![A:$i]:
% 0.33/0.53        ( ( l1_pre_topc @ A ) =>
% 0.33/0.53          ( ![B:$i]:
% 0.33/0.53            ( ( m1_pre_topc @ B @ A ) =>
% 0.33/0.53              ( ~( ( ( u1_struct_0 @ B ) = ( u1_struct_0 @ A ) ) & 
% 0.33/0.53                   ( v1_tex_2 @ B @ A ) ) ) ) ) ) )),
% 0.33/0.53    inference('cnf.neg', [status(esa)], [t15_tex_2])).
% 0.33/0.53  thf('0', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf(t2_tsep_1, axiom,
% 0.33/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.33/0.53  thf('1', plain,
% 0.33/0.53      (![X15 : $i]: ((m1_pre_topc @ X15 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.33/0.53      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.33/0.53  thf(l17_tex_2, axiom,
% 0.33/0.53    (![A:$i]:
% 0.33/0.53     ( ( l1_pre_topc @ A ) =>
% 0.33/0.53       ( ![B:$i]:
% 0.33/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.33/0.53           ( m1_subset_1 @
% 0.33/0.53             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.33/0.53  thf('2', plain,
% 0.33/0.53      (![X18 : $i, X19 : $i]:
% 0.33/0.53         (~ (m1_pre_topc @ X18 @ X19)
% 0.33/0.53          | (m1_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.33/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.33/0.53          | ~ (l1_pre_topc @ X19))),
% 0.33/0.53      inference('cnf', [status(esa)], [l17_tex_2])).
% 0.33/0.53  thf('3', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         (~ (l1_pre_topc @ X0)
% 0.33/0.53          | ~ (l1_pre_topc @ X0)
% 0.33/0.53          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.33/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.33/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.33/0.53  thf('4', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.33/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.33/0.53          | ~ (l1_pre_topc @ X0))),
% 0.33/0.53      inference('simplify', [status(thm)], ['3'])).
% 0.33/0.53  thf(d7_subset_1, axiom,
% 0.33/0.53    (![A:$i,B:$i]:
% 0.33/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.33/0.53       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.33/0.53  thf('5', plain,
% 0.33/0.53      (![X16 : $i, X17 : $i]:
% 0.33/0.53         (~ (v1_subset_1 @ X17 @ X16)
% 0.33/0.53          | ((X17) != (X16))
% 0.33/0.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.33/0.53      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.33/0.53  thf('6', plain,
% 0.33/0.53      (![X16 : $i]:
% 0.33/0.53         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X16))
% 0.33/0.53          | ~ (v1_subset_1 @ X16 @ X16))),
% 0.33/0.53      inference('simplify', [status(thm)], ['5'])).
% 0.33/0.53  thf('7', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         (~ (l1_pre_topc @ X0)
% 0.33/0.53          | ~ (v1_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.33/0.53      inference('sup-', [status(thm)], ['4', '6'])).
% 0.33/0.53  thf('8', plain,
% 0.33/0.53      ((~ (v1_subset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.33/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.33/0.53      inference('sup-', [status(thm)], ['0', '7'])).
% 0.33/0.53  thf('9', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('11', plain,
% 0.33/0.53      (~ (v1_subset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_B_1))),
% 0.33/0.53      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.33/0.53  thf('12', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.33/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.33/0.53          | ~ (l1_pre_topc @ X0))),
% 0.33/0.53      inference('simplify', [status(thm)], ['3'])).
% 0.33/0.53  thf('13', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf(t13_tex_2, axiom,
% 0.33/0.53    (![A:$i]:
% 0.33/0.53     ( ( l1_pre_topc @ A ) =>
% 0.33/0.53       ( ![B:$i]:
% 0.33/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.33/0.53           ( ![C:$i]:
% 0.33/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.33/0.53               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.33/0.53                 ( ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) <=>
% 0.33/0.53                   ( v1_tex_2 @ B @ A ) ) ) ) ) ) ) ))).
% 0.33/0.53  thf('14', plain,
% 0.33/0.53      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.33/0.53         (~ (m1_pre_topc @ X20 @ X21)
% 0.33/0.53          | ((X22) != (u1_struct_0 @ X20))
% 0.33/0.53          | ~ (v1_tex_2 @ X20 @ X21)
% 0.33/0.53          | (v1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.33/0.53          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.33/0.53          | ~ (l1_pre_topc @ X21))),
% 0.33/0.53      inference('cnf', [status(esa)], [t13_tex_2])).
% 0.33/0.53  thf('15', plain,
% 0.33/0.53      (![X20 : $i, X21 : $i]:
% 0.33/0.53         (~ (l1_pre_topc @ X21)
% 0.33/0.53          | ~ (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.33/0.53               (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.33/0.53          | (v1_subset_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))
% 0.33/0.53          | ~ (v1_tex_2 @ X20 @ X21)
% 0.33/0.53          | ~ (m1_pre_topc @ X20 @ X21))),
% 0.33/0.53      inference('simplify', [status(thm)], ['14'])).
% 0.33/0.53  thf('16', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.33/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.33/0.53          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.33/0.53          | ~ (v1_tex_2 @ X0 @ sk_A)
% 0.33/0.53          | (v1_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_A))
% 0.33/0.53          | ~ (l1_pre_topc @ sk_A))),
% 0.33/0.53      inference('sup-', [status(thm)], ['13', '15'])).
% 0.33/0.53  thf('17', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('19', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         (~ (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.33/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1)))
% 0.33/0.53          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.33/0.53          | ~ (v1_tex_2 @ X0 @ sk_A)
% 0.33/0.53          | (v1_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B_1)))),
% 0.33/0.53      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.33/0.53  thf('20', plain,
% 0.33/0.53      ((~ (l1_pre_topc @ sk_B_1)
% 0.33/0.53        | (v1_subset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_B_1))
% 0.33/0.53        | ~ (v1_tex_2 @ sk_B_1 @ sk_A)
% 0.33/0.53        | ~ (m1_pre_topc @ sk_B_1 @ sk_A))),
% 0.33/0.53      inference('sup-', [status(thm)], ['12', '19'])).
% 0.33/0.53  thf('21', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf(dt_m1_pre_topc, axiom,
% 0.33/0.53    (![A:$i]:
% 0.33/0.53     ( ( l1_pre_topc @ A ) =>
% 0.33/0.53       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.33/0.53  thf('22', plain,
% 0.33/0.53      (![X12 : $i, X13 : $i]:
% 0.33/0.53         (~ (m1_pre_topc @ X12 @ X13)
% 0.33/0.53          | (l1_pre_topc @ X12)
% 0.33/0.53          | ~ (l1_pre_topc @ X13))),
% 0.33/0.53      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.33/0.53  thf('23', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B_1))),
% 0.33/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.33/0.53  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('25', plain, ((l1_pre_topc @ sk_B_1)),
% 0.33/0.53      inference('demod', [status(thm)], ['23', '24'])).
% 0.33/0.53  thf('26', plain, ((v1_tex_2 @ sk_B_1 @ sk_A)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('27', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('28', plain,
% 0.33/0.53      ((v1_subset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_B_1))),
% 0.33/0.53      inference('demod', [status(thm)], ['20', '25', '26', '27'])).
% 0.33/0.53  thf('29', plain, ($false), inference('demod', [status(thm)], ['11', '28'])).
% 0.33/0.53  
% 0.33/0.53  % SZS output end Refutation
% 0.33/0.53  
% 0.33/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
