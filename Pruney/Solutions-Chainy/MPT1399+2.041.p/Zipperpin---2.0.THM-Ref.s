%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lvKIRH4bRA

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 (  90 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :   15
%              Number of atoms          :  366 (1106 expanded)
%              Number of equality atoms :    5 (  25 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t28_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ~ ( ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                     => ( ( r2_hidden @ D @ C )
                      <=> ( ( v3_pre_topc @ D @ A )
                          & ( v4_pre_topc @ D @ A )
                          & ( r2_hidden @ B @ D ) ) ) )
                  & ( C = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ~ ( ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ( ( r2_hidden @ D @ C )
                        <=> ( ( v3_pre_topc @ D @ A )
                            & ( v4_pre_topc @ D @ A )
                            & ( r2_hidden @ B @ D ) ) ) )
                    & ( C = k1_xboole_0 ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_connsp_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('5',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','6'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('10',plain,(
    ! [X10: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X10 ) @ X10 )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(fc4_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('11',plain,(
    ! [X8: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X8 ) @ X8 )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X6: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('13',plain,(
    ! [X11: $i] :
      ( ~ ( v3_pre_topc @ X11 @ sk_A )
      | ~ ( v4_pre_topc @ X11 @ sk_A )
      | ~ ( r2_hidden @ sk_B_1 @ X11 )
      | ( r2_hidden @ X11 @ sk_C )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X11: $i] :
      ( ~ ( v3_pre_topc @ X11 @ sk_A )
      | ~ ( v4_pre_topc @ X11 @ sk_A )
      | ~ ( r2_hidden @ sk_B_1 @ X11 )
      | ( r2_hidden @ X11 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('18',plain,
    ( ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( k2_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( k2_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','26'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('31',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('32',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('35',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lvKIRH4bRA
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:42:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 51 iterations in 0.025s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.47  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.47  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.47  thf(t28_connsp_2, conjecture,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.47           ( ![C:$i]:
% 0.21/0.47             ( ( m1_subset_1 @
% 0.21/0.47                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.47               ( ~( ( ![D:$i]:
% 0.21/0.47                      ( ( m1_subset_1 @
% 0.21/0.47                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47                        ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.47                          ( ( v3_pre_topc @ D @ A ) & 
% 0.21/0.47                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.21/0.47                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i]:
% 0.21/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.47            ( l1_pre_topc @ A ) ) =>
% 0.21/0.47          ( ![B:$i]:
% 0.21/0.47            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.47              ( ![C:$i]:
% 0.21/0.47                ( ( m1_subset_1 @
% 0.21/0.47                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.47                  ( ~( ( ![D:$i]:
% 0.21/0.47                         ( ( m1_subset_1 @
% 0.21/0.47                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.47                           ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.47                             ( ( v3_pre_topc @ D @ A ) & 
% 0.21/0.47                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.21/0.47                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.21/0.47  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(d3_struct_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X5 : $i]:
% 0.21/0.47         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.21/0.47      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.47  thf('2', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (((m1_subset_1 @ sk_B_1 @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(dt_l1_pre_topc, axiom,
% 0.21/0.47    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.47  thf('5', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.47  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('7', plain, ((m1_subset_1 @ sk_B_1 @ (k2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '6'])).
% 0.21/0.47  thf(t2_subset, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.47       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i]:
% 0.21/0.47         ((r2_hidden @ X3 @ X4)
% 0.21/0.47          | (v1_xboole_0 @ X4)
% 0.21/0.47          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.47        | (r2_hidden @ sk_B_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.47  thf(fc10_tops_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X10 : $i]:
% 0.21/0.47         ((v3_pre_topc @ (k2_struct_0 @ X10) @ X10)
% 0.21/0.47          | ~ (l1_pre_topc @ X10)
% 0.21/0.47          | ~ (v2_pre_topc @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.21/0.47  thf(fc4_pre_topc, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.47       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X8 : $i]:
% 0.21/0.47         ((v4_pre_topc @ (k2_struct_0 @ X8) @ X8)
% 0.21/0.47          | ~ (l1_pre_topc @ X8)
% 0.21/0.47          | ~ (v2_pre_topc @ X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.21/0.47  thf(dt_k2_struct_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( l1_struct_0 @ A ) =>
% 0.21/0.47       ( m1_subset_1 @
% 0.21/0.47         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X6 : $i]:
% 0.21/0.47         ((m1_subset_1 @ (k2_struct_0 @ X6) @ 
% 0.21/0.47           (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.47          | ~ (l1_struct_0 @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X11 : $i]:
% 0.21/0.47         (~ (v3_pre_topc @ X11 @ sk_A)
% 0.21/0.47          | ~ (v4_pre_topc @ X11 @ sk_A)
% 0.21/0.47          | ~ (r2_hidden @ sk_B_1 @ X11)
% 0.21/0.47          | (r2_hidden @ X11 @ sk_C)
% 0.21/0.47          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('14', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      (![X11 : $i]:
% 0.21/0.47         (~ (v3_pre_topc @ X11 @ sk_A)
% 0.21/0.47          | ~ (v4_pre_topc @ X11 @ sk_A)
% 0.21/0.47          | ~ (r2_hidden @ sk_B_1 @ X11)
% 0.21/0.47          | (r2_hidden @ X11 @ k1_xboole_0)
% 0.21/0.47          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.47      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      ((~ (l1_struct_0 @ sk_A)
% 0.21/0.47        | (r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 0.21/0.47        | ~ (r2_hidden @ sk_B_1 @ (k2_struct_0 @ sk_A))
% 0.21/0.47        | ~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.21/0.47        | ~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['12', '15'])).
% 0.21/0.47  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (((r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 0.21/0.47        | ~ (r2_hidden @ sk_B_1 @ (k2_struct_0 @ sk_A))
% 0.21/0.47        | ~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.21/0.47        | ~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.47        | ~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.21/0.47        | ~ (r2_hidden @ sk_B_1 @ (k2_struct_0 @ sk_A))
% 0.21/0.47        | (r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['11', '18'])).
% 0.21/0.47  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.21/0.47        | ~ (r2_hidden @ sk_B_1 @ (k2_struct_0 @ sk_A))
% 0.21/0.47        | (r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.21/0.47      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.47        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.47        | (r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 0.21/0.47        | ~ (r2_hidden @ sk_B_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['10', '22'])).
% 0.21/0.47  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      (((r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 0.21/0.47        | ~ (r2_hidden @ sk_B_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.47      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.21/0.47        | (r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['9', '26'])).
% 0.21/0.47  thf(d1_xboole_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.47  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.47  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.47  thf('31', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.47  thf(fc5_struct_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.47       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.21/0.47  thf('32', plain,
% 0.21/0.47      (![X9 : $i]:
% 0.21/0.47         (~ (v1_xboole_0 @ (k2_struct_0 @ X9))
% 0.21/0.47          | ~ (l1_struct_0 @ X9)
% 0.21/0.47          | (v2_struct_0 @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.21/0.47  thf('33', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.47  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.47  thf('35', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.47      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.47  thf('36', plain, ($false), inference('demod', [status(thm)], ['0', '35'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
