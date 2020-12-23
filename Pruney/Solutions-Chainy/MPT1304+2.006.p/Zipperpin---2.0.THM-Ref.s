%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mg9CYxNHMZ

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:21 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   50 (  62 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  368 ( 630 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(t22_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( v1_tops_2 @ B @ A )
               => ( v1_tops_2 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( ( v1_tops_2 @ B @ A )
                 => ( v1_tops_2 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t22_tops_2])).

thf('0',plain,(
    ~ ( v1_tops_2 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( ( k7_subset_1 @ X24 @ X23 @ X25 )
        = ( k4_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X16 )
      | ( X16
       != ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X19 ) @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('14',plain,(
    r1_tarski @ ( k1_zfmisc_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X30: $i,X32: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( r1_tarski @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,(
    m1_subset_1 @ ( k1_zfmisc_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('17',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( m1_subset_1 @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf(t18_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( ( r1_tarski @ B @ C )
                  & ( v1_tops_2 @ C @ A ) )
               => ( v1_tops_2 @ B @ A ) ) ) ) ) )).

thf('20',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) ) )
      | ( v1_tops_2 @ X39 @ X40 )
      | ~ ( r1_tarski @ X39 @ X41 )
      | ~ ( v1_tops_2 @ X41 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[t18_tops_2])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v1_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','23'])).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('26',plain,(
    v1_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( v1_tops_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['4','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mg9CYxNHMZ
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:35:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.68/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.88  % Solved by: fo/fo7.sh
% 0.68/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.88  % done 1076 iterations in 0.427s
% 0.68/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.88  % SZS output start Refutation
% 0.68/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.88  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.68/0.88  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.68/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.88  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.68/0.88  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.68/0.88  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.68/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.88  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.68/0.88  thf(t22_tops_2, conjecture,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( l1_pre_topc @ A ) =>
% 0.68/0.88       ( ![B:$i]:
% 0.68/0.88         ( ( m1_subset_1 @
% 0.68/0.88             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.68/0.88           ( ![C:$i]:
% 0.68/0.88             ( ( m1_subset_1 @
% 0.68/0.88                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.68/0.88               ( ( v1_tops_2 @ B @ A ) =>
% 0.68/0.88                 ( v1_tops_2 @
% 0.68/0.88                   ( k7_subset_1 @
% 0.68/0.88                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.68/0.88                   A ) ) ) ) ) ) ))).
% 0.68/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.88    (~( ![A:$i]:
% 0.68/0.88        ( ( l1_pre_topc @ A ) =>
% 0.68/0.88          ( ![B:$i]:
% 0.68/0.88            ( ( m1_subset_1 @
% 0.68/0.88                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.68/0.88              ( ![C:$i]:
% 0.68/0.88                ( ( m1_subset_1 @
% 0.68/0.88                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.68/0.88                  ( ( v1_tops_2 @ B @ A ) =>
% 0.68/0.88                    ( v1_tops_2 @
% 0.68/0.88                      ( k7_subset_1 @
% 0.68/0.88                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.68/0.88                      A ) ) ) ) ) ) ) )),
% 0.68/0.88    inference('cnf.neg', [status(esa)], [t22_tops_2])).
% 0.68/0.88  thf('0', plain,
% 0.68/0.88      (~ (v1_tops_2 @ 
% 0.68/0.88          (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1) @ 
% 0.68/0.88          sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('1', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_B @ 
% 0.68/0.88        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(redefinition_k7_subset_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.88       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.68/0.88  thf('2', plain,
% 0.68/0.88      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.68/0.88          | ((k7_subset_1 @ X24 @ X23 @ X25) = (k4_xboole_0 @ X23 @ X25)))),
% 0.68/0.88      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.68/0.88  thf('3', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 0.68/0.88           = (k4_xboole_0 @ sk_B @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['1', '2'])).
% 0.68/0.88  thf('4', plain, (~ (v1_tops_2 @ (k4_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 0.68/0.88      inference('demod', [status(thm)], ['0', '3'])).
% 0.68/0.88  thf('5', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_B @ 
% 0.68/0.88        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(t36_xboole_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.68/0.88  thf('6', plain,
% 0.68/0.88      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 0.68/0.88      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.68/0.88  thf(d1_zfmisc_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.68/0.88       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.68/0.88  thf('7', plain,
% 0.68/0.88      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.68/0.88         (~ (r1_tarski @ X14 @ X15)
% 0.68/0.88          | (r2_hidden @ X14 @ X16)
% 0.68/0.88          | ((X16) != (k1_zfmisc_1 @ X15)))),
% 0.68/0.88      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.68/0.88  thf('8', plain,
% 0.68/0.88      (![X14 : $i, X15 : $i]:
% 0.68/0.88         ((r2_hidden @ X14 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X14 @ X15))),
% 0.68/0.88      inference('simplify', [status(thm)], ['7'])).
% 0.68/0.88  thf('9', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         (r2_hidden @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['6', '8'])).
% 0.68/0.88  thf('10', plain,
% 0.68/0.88      ((m1_subset_1 @ sk_B @ 
% 0.68/0.88        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf(t3_subset, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.68/0.88  thf('11', plain,
% 0.68/0.88      (![X30 : $i, X31 : $i]:
% 0.68/0.88         ((r1_tarski @ X30 @ X31) | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t3_subset])).
% 0.68/0.88  thf('12', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['10', '11'])).
% 0.68/0.88  thf(t79_zfmisc_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( r1_tarski @ A @ B ) =>
% 0.68/0.88       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.68/0.88  thf('13', plain,
% 0.68/0.88      (![X19 : $i, X20 : $i]:
% 0.68/0.88         ((r1_tarski @ (k1_zfmisc_1 @ X19) @ (k1_zfmisc_1 @ X20))
% 0.68/0.88          | ~ (r1_tarski @ X19 @ X20))),
% 0.68/0.88      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.68/0.88  thf('14', plain,
% 0.68/0.88      ((r1_tarski @ (k1_zfmisc_1 @ sk_B) @ 
% 0.68/0.88        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['12', '13'])).
% 0.68/0.88  thf('15', plain,
% 0.68/0.88      (![X30 : $i, X32 : $i]:
% 0.68/0.88         ((m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X32)) | ~ (r1_tarski @ X30 @ X32))),
% 0.68/0.88      inference('cnf', [status(esa)], [t3_subset])).
% 0.68/0.88  thf('16', plain,
% 0.68/0.88      ((m1_subset_1 @ (k1_zfmisc_1 @ sk_B) @ 
% 0.68/0.88        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['14', '15'])).
% 0.68/0.88  thf(t4_subset, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.68/0.88       ( m1_subset_1 @ A @ C ) ))).
% 0.68/0.88  thf('17', plain,
% 0.68/0.88      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.68/0.88         (~ (r2_hidden @ X33 @ X34)
% 0.68/0.88          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.68/0.88          | (m1_subset_1 @ X33 @ X35))),
% 0.68/0.88      inference('cnf', [status(esa)], [t4_subset])).
% 0.68/0.88  thf('18', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((m1_subset_1 @ X0 @ 
% 0.68/0.88           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.68/0.88          | ~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_B)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['16', '17'])).
% 0.68/0.88  thf('19', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.68/0.88          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['9', '18'])).
% 0.68/0.88  thf(t18_tops_2, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( l1_pre_topc @ A ) =>
% 0.68/0.88       ( ![B:$i]:
% 0.68/0.88         ( ( m1_subset_1 @
% 0.68/0.88             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.68/0.88           ( ![C:$i]:
% 0.68/0.88             ( ( m1_subset_1 @
% 0.68/0.88                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.68/0.88               ( ( ( r1_tarski @ B @ C ) & ( v1_tops_2 @ C @ A ) ) =>
% 0.68/0.88                 ( v1_tops_2 @ B @ A ) ) ) ) ) ) ))).
% 0.68/0.88  thf('20', plain,
% 0.68/0.88      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X39 @ 
% 0.68/0.88             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40))))
% 0.68/0.88          | (v1_tops_2 @ X39 @ X40)
% 0.68/0.88          | ~ (r1_tarski @ X39 @ X41)
% 0.68/0.88          | ~ (v1_tops_2 @ X41 @ X40)
% 0.68/0.88          | ~ (m1_subset_1 @ X41 @ 
% 0.68/0.88               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40))))
% 0.68/0.88          | ~ (l1_pre_topc @ X40))),
% 0.68/0.88      inference('cnf', [status(esa)], [t18_tops_2])).
% 0.68/0.88  thf('21', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         (~ (l1_pre_topc @ sk_A)
% 0.68/0.88          | ~ (m1_subset_1 @ X1 @ 
% 0.68/0.88               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.68/0.88          | ~ (v1_tops_2 @ X1 @ sk_A)
% 0.68/0.88          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1)
% 0.68/0.88          | (v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['19', '20'])).
% 0.68/0.88  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('23', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X1 @ 
% 0.68/0.88             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.68/0.88          | ~ (v1_tops_2 @ X1 @ sk_A)
% 0.68/0.88          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1)
% 0.68/0.88          | (v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.68/0.88      inference('demod', [status(thm)], ['21', '22'])).
% 0.68/0.88  thf('24', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.68/0.88          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_B)
% 0.68/0.88          | ~ (v1_tops_2 @ sk_B @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['5', '23'])).
% 0.68/0.88  thf('25', plain,
% 0.68/0.88      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 0.68/0.88      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.68/0.88  thf('26', plain, ((v1_tops_2 @ sk_B @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('27', plain,
% 0.68/0.88      (![X0 : $i]: (v1_tops_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)),
% 0.68/0.88      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.68/0.88  thf('28', plain, ($false), inference('demod', [status(thm)], ['4', '27'])).
% 0.68/0.88  
% 0.68/0.88  % SZS output end Refutation
% 0.68/0.88  
% 0.68/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
