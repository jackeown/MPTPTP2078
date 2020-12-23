%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.80NGuxCLl2

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:08 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   64 (  90 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :   15
%              Number of atoms          :  378 (1118 expanded)
%              Number of equality atoms :    5 (  25 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('6',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('7',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k2_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('9',plain,(
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

thf('10',plain,(
    ! [X9: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X9 ) @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc4_pre_topc])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('11',plain,(
    ! [X6: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('12',plain,(
    ! [X11: $i] :
      ( ~ ( v3_pre_topc @ X11 @ sk_A )
      | ~ ( v4_pre_topc @ X11 @ sk_A )
      | ~ ( r2_hidden @ sk_B_1 @ X11 )
      | ( r2_hidden @ X11 @ sk_C )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_C = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X11: $i] :
      ( ~ ( v3_pre_topc @ X11 @ sk_A )
      | ~ ( v4_pre_topc @ X11 @ sk_A )
      | ~ ( r2_hidden @ sk_B_1 @ X11 )
      | ( r2_hidden @ X11 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('17',plain,
    ( ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( k2_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B_1 @ ( k2_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','21'])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','25'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('27',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('28',plain,
    ( ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('30',plain,
    ( ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['30','31'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('34',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['34','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.80NGuxCLl2
% 0.13/0.37  % Computer   : n015.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 17:59:38 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.23/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.48  % Solved by: fo/fo7.sh
% 0.23/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.48  % done 51 iterations in 0.026s
% 0.23/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.48  % SZS output start Refutation
% 0.23/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.23/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.23/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.23/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.48  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.23/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.23/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.48  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.23/0.48  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.23/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.23/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.23/0.48  thf(d3_struct_0, axiom,
% 0.23/0.48    (![A:$i]:
% 0.23/0.48     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.23/0.48  thf('0', plain,
% 0.23/0.48      (![X5 : $i]:
% 0.23/0.48         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.23/0.48      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.23/0.48  thf(t28_connsp_2, conjecture,
% 0.23/0.48    (![A:$i]:
% 0.23/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.48       ( ![B:$i]:
% 0.23/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.48           ( ![C:$i]:
% 0.23/0.48             ( ( m1_subset_1 @
% 0.23/0.48                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.23/0.48               ( ~( ( ![D:$i]:
% 0.23/0.48                      ( ( m1_subset_1 @
% 0.23/0.48                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.48                        ( ( r2_hidden @ D @ C ) <=>
% 0.23/0.48                          ( ( v3_pre_topc @ D @ A ) & 
% 0.23/0.48                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.23/0.48                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.23/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.48    (~( ![A:$i]:
% 0.23/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.23/0.48            ( l1_pre_topc @ A ) ) =>
% 0.23/0.48          ( ![B:$i]:
% 0.23/0.48            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.23/0.48              ( ![C:$i]:
% 0.23/0.48                ( ( m1_subset_1 @
% 0.23/0.48                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.23/0.48                  ( ~( ( ![D:$i]:
% 0.23/0.48                         ( ( m1_subset_1 @
% 0.23/0.48                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.23/0.48                           ( ( r2_hidden @ D @ C ) <=>
% 0.23/0.48                             ( ( v3_pre_topc @ D @ A ) & 
% 0.23/0.48                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.23/0.48                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.23/0.48    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.23/0.48  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf(t2_subset, axiom,
% 0.23/0.48    (![A:$i,B:$i]:
% 0.23/0.48     ( ( m1_subset_1 @ A @ B ) =>
% 0.23/0.48       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.23/0.48  thf('2', plain,
% 0.23/0.48      (![X3 : $i, X4 : $i]:
% 0.23/0.48         ((r2_hidden @ X3 @ X4)
% 0.23/0.48          | (v1_xboole_0 @ X4)
% 0.23/0.48          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.23/0.48      inference('cnf', [status(esa)], [t2_subset])).
% 0.23/0.48  thf('3', plain,
% 0.23/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.48        | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.23/0.48  thf('4', plain,
% 0.23/0.48      (((r2_hidden @ sk_B_1 @ (k2_struct_0 @ sk_A))
% 0.23/0.48        | ~ (l1_struct_0 @ sk_A)
% 0.23/0.48        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.48      inference('sup+', [status(thm)], ['0', '3'])).
% 0.23/0.48  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf(dt_l1_pre_topc, axiom,
% 0.23/0.48    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.23/0.48  thf('6', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.23/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.23/0.48  thf('7', plain, ((l1_struct_0 @ sk_A)),
% 0.23/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.48  thf('8', plain,
% 0.23/0.48      (((r2_hidden @ sk_B_1 @ (k2_struct_0 @ sk_A))
% 0.23/0.48        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.23/0.48      inference('demod', [status(thm)], ['4', '7'])).
% 0.23/0.48  thf(fc10_tops_1, axiom,
% 0.23/0.48    (![A:$i]:
% 0.23/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.48       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.23/0.48  thf('9', plain,
% 0.23/0.48      (![X10 : $i]:
% 0.23/0.48         ((v3_pre_topc @ (k2_struct_0 @ X10) @ X10)
% 0.23/0.48          | ~ (l1_pre_topc @ X10)
% 0.23/0.48          | ~ (v2_pre_topc @ X10))),
% 0.23/0.48      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.23/0.48  thf(fc4_pre_topc, axiom,
% 0.23/0.48    (![A:$i]:
% 0.23/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.23/0.48       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.23/0.48  thf('10', plain,
% 0.23/0.48      (![X9 : $i]:
% 0.23/0.48         ((v4_pre_topc @ (k2_struct_0 @ X9) @ X9)
% 0.23/0.48          | ~ (l1_pre_topc @ X9)
% 0.23/0.48          | ~ (v2_pre_topc @ X9))),
% 0.23/0.48      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.23/0.48  thf(dt_k2_struct_0, axiom,
% 0.23/0.48    (![A:$i]:
% 0.23/0.48     ( ( l1_struct_0 @ A ) =>
% 0.23/0.48       ( m1_subset_1 @
% 0.23/0.48         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.23/0.48  thf('11', plain,
% 0.23/0.48      (![X6 : $i]:
% 0.23/0.48         ((m1_subset_1 @ (k2_struct_0 @ X6) @ 
% 0.23/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.23/0.48          | ~ (l1_struct_0 @ X6))),
% 0.23/0.48      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.23/0.48  thf('12', plain,
% 0.23/0.48      (![X11 : $i]:
% 0.23/0.48         (~ (v3_pre_topc @ X11 @ sk_A)
% 0.23/0.48          | ~ (v4_pre_topc @ X11 @ sk_A)
% 0.23/0.48          | ~ (r2_hidden @ sk_B_1 @ X11)
% 0.23/0.48          | (r2_hidden @ X11 @ sk_C)
% 0.23/0.48          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('13', plain, (((sk_C) = (k1_xboole_0))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('14', plain,
% 0.23/0.48      (![X11 : $i]:
% 0.23/0.48         (~ (v3_pre_topc @ X11 @ sk_A)
% 0.23/0.48          | ~ (v4_pre_topc @ X11 @ sk_A)
% 0.23/0.48          | ~ (r2_hidden @ sk_B_1 @ X11)
% 0.23/0.48          | (r2_hidden @ X11 @ k1_xboole_0)
% 0.23/0.48          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.23/0.48      inference('demod', [status(thm)], ['12', '13'])).
% 0.23/0.48  thf('15', plain,
% 0.23/0.48      ((~ (l1_struct_0 @ sk_A)
% 0.23/0.48        | (r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 0.23/0.48        | ~ (r2_hidden @ sk_B_1 @ (k2_struct_0 @ sk_A))
% 0.23/0.48        | ~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.23/0.48        | ~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A))),
% 0.23/0.48      inference('sup-', [status(thm)], ['11', '14'])).
% 0.23/0.48  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 0.23/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.48  thf('17', plain,
% 0.23/0.48      (((r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 0.23/0.48        | ~ (r2_hidden @ sk_B_1 @ (k2_struct_0 @ sk_A))
% 0.23/0.48        | ~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.23/0.48        | ~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A))),
% 0.23/0.48      inference('demod', [status(thm)], ['15', '16'])).
% 0.23/0.48  thf('18', plain,
% 0.23/0.48      ((~ (v2_pre_topc @ sk_A)
% 0.23/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.48        | ~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.23/0.48        | ~ (r2_hidden @ sk_B_1 @ (k2_struct_0 @ sk_A))
% 0.23/0.48        | (r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.23/0.48      inference('sup-', [status(thm)], ['10', '17'])).
% 0.23/0.48  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('21', plain,
% 0.23/0.48      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.23/0.48        | ~ (r2_hidden @ sk_B_1 @ (k2_struct_0 @ sk_A))
% 0.23/0.48        | (r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.23/0.48      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.23/0.48  thf('22', plain,
% 0.23/0.48      ((~ (v2_pre_topc @ sk_A)
% 0.23/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.23/0.48        | (r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 0.23/0.48        | ~ (r2_hidden @ sk_B_1 @ (k2_struct_0 @ sk_A)))),
% 0.23/0.48      inference('sup-', [status(thm)], ['9', '21'])).
% 0.23/0.48  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('25', plain,
% 0.23/0.48      (((r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 0.23/0.48        | ~ (r2_hidden @ sk_B_1 @ (k2_struct_0 @ sk_A)))),
% 0.23/0.48      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.23/0.48  thf('26', plain,
% 0.23/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.23/0.48        | (r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.23/0.48      inference('sup-', [status(thm)], ['8', '25'])).
% 0.23/0.48  thf(fc2_struct_0, axiom,
% 0.23/0.48    (![A:$i]:
% 0.23/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.23/0.48       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.23/0.48  thf('27', plain,
% 0.23/0.48      (![X8 : $i]:
% 0.23/0.48         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.23/0.48          | ~ (l1_struct_0 @ X8)
% 0.23/0.48          | (v2_struct_0 @ X8))),
% 0.23/0.48      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.23/0.48  thf('28', plain,
% 0.23/0.48      (((r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 0.23/0.48        | (v2_struct_0 @ sk_A)
% 0.23/0.48        | ~ (l1_struct_0 @ sk_A))),
% 0.23/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.23/0.48  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 0.23/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.48  thf('30', plain,
% 0.23/0.48      (((r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0) | (v2_struct_0 @ sk_A))),
% 0.23/0.48      inference('demod', [status(thm)], ['28', '29'])).
% 0.23/0.48  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('32', plain, ((r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0)),
% 0.23/0.48      inference('clc', [status(thm)], ['30', '31'])).
% 0.23/0.48  thf(d1_xboole_0, axiom,
% 0.23/0.48    (![A:$i]:
% 0.23/0.48     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.23/0.48  thf('33', plain,
% 0.23/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.23/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.23/0.48  thf('34', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.23/0.48      inference('sup-', [status(thm)], ['32', '33'])).
% 0.23/0.48  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.23/0.48  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.23/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.23/0.48  thf('36', plain, ($false), inference('demod', [status(thm)], ['34', '35'])).
% 0.23/0.48  
% 0.23/0.48  % SZS output end Refutation
% 0.23/0.48  
% 0.23/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
