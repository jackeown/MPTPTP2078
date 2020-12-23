%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nGxhfzeXK9

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  63 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  316 ( 550 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(t43_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( m1_pre_topc @ X3 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(l17_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
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

thf(t27_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( B
              = ( u1_struct_0 @ A ) )
           => ( ( v2_tex_2 @ B @ A )
            <=> ( v1_tdlat_3 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v1_tdlat_3 @ X7 )
      | ( v2_tex_2 @ X6 @ X7 )
      | ( X6
       != ( u1_struct_0 @ X7 ) )
      | ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t27_tex_2])).

thf('6',plain,(
    ! [X7: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X7 ) @ X7 )
      | ~ ( v1_tdlat_3 @ X7 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t28_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( r1_tarski @ C @ B )
                  & ( v2_tex_2 @ B @ A ) )
               => ( v2_tex_2 @ C @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v2_tex_2 @ X8 @ X9 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ( v2_tex_2 @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['14','15','18'])).

thf('20',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['0','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nGxhfzeXK9
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:54:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 23 iterations in 0.016s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.47  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.47  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.21/0.47  thf(t43_tex_2, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 0.21/0.47         ( l1_pre_topc @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.47            ( v1_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t43_tex_2])).
% 0.21/0.47  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t2_tsep_1, axiom,
% 0.21/0.47    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X3 : $i]: ((m1_pre_topc @ X3 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.21/0.47  thf(l17_tex_2, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_pre_topc @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.47           ( m1_subset_1 @
% 0.21/0.47             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i]:
% 0.21/0.47         (~ (m1_pre_topc @ X4 @ X5)
% 0.21/0.47          | (m1_subset_1 @ (u1_struct_0 @ X4) @ 
% 0.21/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.21/0.47          | ~ (l1_pre_topc @ X5))),
% 0.21/0.47      inference('cnf', [status(esa)], [l17_tex_2])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (l1_pre_topc @ X0)
% 0.21/0.47          | ~ (l1_pre_topc @ X0)
% 0.21/0.47          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.21/0.47             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.21/0.47           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.47          | ~ (l1_pre_topc @ X0))),
% 0.21/0.47      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.47  thf(t27_tex_2, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47           ( ( ( B ) = ( u1_struct_0 @ A ) ) =>
% 0.21/0.47             ( ( v2_tex_2 @ B @ A ) <=> ( v1_tdlat_3 @ A ) ) ) ) ) ))).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.21/0.47          | ~ (v1_tdlat_3 @ X7)
% 0.21/0.47          | (v2_tex_2 @ X6 @ X7)
% 0.21/0.47          | ((X6) != (u1_struct_0 @ X7))
% 0.21/0.47          | ~ (l1_pre_topc @ X7)
% 0.21/0.47          | (v2_struct_0 @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [t27_tex_2])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X7 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X7)
% 0.21/0.47          | ~ (l1_pre_topc @ X7)
% 0.21/0.47          | (v2_tex_2 @ (u1_struct_0 @ X7) @ X7)
% 0.21/0.47          | ~ (v1_tdlat_3 @ X7)
% 0.21/0.47          | ~ (m1_subset_1 @ (u1_struct_0 @ X7) @ 
% 0.21/0.47               (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.21/0.47      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (~ (l1_pre_topc @ X0)
% 0.21/0.47          | ~ (v1_tdlat_3 @ X0)
% 0.21/0.47          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.47          | ~ (l1_pre_topc @ X0)
% 0.21/0.47          | (v2_struct_0 @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '6'])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((v2_struct_0 @ X0)
% 0.21/0.47          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.47          | ~ (v1_tdlat_3 @ X0)
% 0.21/0.47          | ~ (l1_pre_topc @ X0))),
% 0.21/0.47      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.21/0.47           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.47          | ~ (l1_pre_topc @ X0))),
% 0.21/0.47      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.47  thf(t28_tex_2, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_pre_topc @ A ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47               ( ( ( r1_tarski @ C @ B ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.21/0.47                 ( v2_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.47         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.47          | ~ (v2_tex_2 @ X8 @ X9)
% 0.21/0.47          | ~ (r1_tarski @ X10 @ X8)
% 0.21/0.47          | (v2_tex_2 @ X10 @ X9)
% 0.21/0.47          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.21/0.47          | ~ (l1_pre_topc @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (l1_pre_topc @ X0)
% 0.21/0.47          | ~ (l1_pre_topc @ X0)
% 0.21/0.47          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.47          | (v2_tex_2 @ X1 @ X0)
% 0.21/0.47          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.47          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 0.21/0.47          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.47          | (v2_tex_2 @ X1 @ X0)
% 0.21/0.47          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.47          | ~ (l1_pre_topc @ X0))),
% 0.21/0.47      inference('simplify', [status(thm)], ['12'])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.47        | (v2_tex_2 @ sk_B @ sk_A)
% 0.21/0.47        | ~ (r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))
% 0.21/0.47        | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['9', '13'])).
% 0.21/0.47  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t3_subset, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.47  thf('18', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (((v2_tex_2 @ sk_B @ sk_A) | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['14', '15', '18'])).
% 0.21/0.47  thf('20', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('21', plain, (~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)),
% 0.21/0.47      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      ((~ (l1_pre_topc @ sk_A) | ~ (v1_tdlat_3 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '21'])).
% 0.21/0.47  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('24', plain, ((v1_tdlat_3 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('25', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.21/0.47  thf('26', plain, ($false), inference('demod', [status(thm)], ['0', '25'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
