%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Vi2VsXBMtq

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 (  91 expanded)
%              Number of leaves         :   27 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  378 (1118 expanded)
%              Number of equality atoms :    5 (  25 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('7',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('8',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','8'])).

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
    ! [X9: $i] :
      ( ( v4_pre_topc @ ( k2_struct_0 @ X9 ) @ X9 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
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
      | ~ ( r2_hidden @ sk_B @ X11 )
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
      | ~ ( r2_hidden @ sk_B @ X11 )
      | ( r2_hidden @ X11 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('18',plain,
    ( ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( r2_hidden @ sk_B @ ( k2_struct_0 @ sk_A ) )
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
    | ~ ( r2_hidden @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
    | ~ ( r2_hidden @ sk_B @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','26'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ k1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('31',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('32',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['6','7'])).

thf('35',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Vi2VsXBMtq
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:39:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 59 iterations in 0.028s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.48  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.48  thf(t28_connsp_2, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( m1_subset_1 @
% 0.21/0.48                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.48               ( ~( ( ![D:$i]:
% 0.21/0.48                      ( ( m1_subset_1 @
% 0.21/0.48                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48                        ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.48                          ( ( v3_pre_topc @ D @ A ) & 
% 0.21/0.48                            ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.21/0.48                    ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.48            ( l1_pre_topc @ A ) ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.48              ( ![C:$i]:
% 0.21/0.48                ( ( m1_subset_1 @
% 0.21/0.48                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.48                  ( ~( ( ![D:$i]:
% 0.21/0.48                         ( ( m1_subset_1 @
% 0.21/0.48                             D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.48                           ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.48                             ( ( v3_pre_topc @ D @ A ) & 
% 0.21/0.48                               ( v4_pre_topc @ D @ A ) & ( r2_hidden @ B @ D ) ) ) ) ) & 
% 0.21/0.48                       ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t28_connsp_2])).
% 0.21/0.48  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d3_struct_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X5 : $i]:
% 0.21/0.48         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.48  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t2_subset, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.48       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X1 : $i, X2 : $i]:
% 0.21/0.48         ((r2_hidden @ X1 @ X2)
% 0.21/0.48          | (v1_xboole_0 @ X2)
% 0.21/0.48          | ~ (m1_subset_1 @ X1 @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.48        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (((r2_hidden @ sk_B @ (k2_struct_0 @ sk_A))
% 0.21/0.48        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.48        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['1', '4'])).
% 0.21/0.48  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(dt_l1_pre_topc, axiom,
% 0.21/0.48    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.48  thf('7', plain, (![X7 : $i]: ((l1_struct_0 @ X7) | ~ (l1_pre_topc @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('8', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (((r2_hidden @ sk_B @ (k2_struct_0 @ sk_A))
% 0.21/0.48        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['5', '8'])).
% 0.21/0.48  thf(fc10_tops_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X10 : $i]:
% 0.21/0.48         ((v3_pre_topc @ (k2_struct_0 @ X10) @ X10)
% 0.21/0.48          | ~ (l1_pre_topc @ X10)
% 0.21/0.48          | ~ (v2_pre_topc @ X10))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.21/0.48  thf(fc4_pre_topc, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( v4_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X9 : $i]:
% 0.21/0.48         ((v4_pre_topc @ (k2_struct_0 @ X9) @ X9)
% 0.21/0.48          | ~ (l1_pre_topc @ X9)
% 0.21/0.48          | ~ (v2_pre_topc @ X9))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc4_pre_topc])).
% 0.21/0.48  thf(dt_k2_struct_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_struct_0 @ A ) =>
% 0.21/0.48       ( m1_subset_1 @
% 0.21/0.48         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X6 : $i]:
% 0.21/0.48         ((m1_subset_1 @ (k2_struct_0 @ X6) @ 
% 0.21/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.48          | ~ (l1_struct_0 @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X11 : $i]:
% 0.21/0.48         (~ (v3_pre_topc @ X11 @ sk_A)
% 0.21/0.48          | ~ (v4_pre_topc @ X11 @ sk_A)
% 0.21/0.48          | ~ (r2_hidden @ sk_B @ X11)
% 0.21/0.48          | (r2_hidden @ X11 @ sk_C)
% 0.21/0.48          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('14', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X11 : $i]:
% 0.21/0.48         (~ (v3_pre_topc @ X11 @ sk_A)
% 0.21/0.48          | ~ (v4_pre_topc @ X11 @ sk_A)
% 0.21/0.48          | ~ (r2_hidden @ sk_B @ X11)
% 0.21/0.48          | (r2_hidden @ X11 @ k1_xboole_0)
% 0.21/0.48          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      ((~ (l1_struct_0 @ sk_A)
% 0.21/0.48        | (r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 0.21/0.48        | ~ (r2_hidden @ sk_B @ (k2_struct_0 @ sk_A))
% 0.21/0.48        | ~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.21/0.48        | ~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['12', '15'])).
% 0.21/0.48  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (((r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 0.21/0.48        | ~ (r2_hidden @ sk_B @ (k2_struct_0 @ sk_A))
% 0.21/0.48        | ~ (v4_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.21/0.48        | ~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | ~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.21/0.48        | ~ (r2_hidden @ sk_B @ (k2_struct_0 @ sk_A))
% 0.21/0.48        | (r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['11', '18'])).
% 0.21/0.48  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)
% 0.21/0.48        | ~ (r2_hidden @ sk_B @ (k2_struct_0 @ sk_A))
% 0.21/0.48        | (r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.21/0.48      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      ((~ (v2_pre_topc @ sk_A)
% 0.21/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.48        | (r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 0.21/0.48        | ~ (r2_hidden @ sk_B @ (k2_struct_0 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '22'])).
% 0.21/0.48  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (((r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 0.21/0.48        | ~ (r2_hidden @ sk_B @ (k2_struct_0 @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.48        | (r2_hidden @ (k2_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['9', '26'])).
% 0.21/0.48  thf(t7_ordinal1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i]: (~ (r2_hidden @ X3 @ X4) | ~ (r1_tarski @ X4 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.48        | ~ (r1_tarski @ k1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.48  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.48  thf('30', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.48  thf('31', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.48  thf(fc2_struct_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.48       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (![X8 : $i]:
% 0.21/0.48         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.21/0.48          | ~ (l1_struct_0 @ X8)
% 0.21/0.48          | (v2_struct_0 @ X8))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.48  thf('33', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.48  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('35', plain, ((v2_struct_0 @ sk_A)),
% 0.21/0.48      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.48  thf('36', plain, ($false), inference('demod', [status(thm)], ['0', '35'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
