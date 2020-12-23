%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9FAV7LPGcR

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 102 expanded)
%              Number of leaves         :   18 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :  520 (1855 expanded)
%              Number of equality atoms :   19 (  63 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t34_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v4_pre_topc @ B @ A )
                  & ( v4_pre_topc @ C @ A ) )
               => ( ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) )
                  = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v4_pre_topc @ B @ A )
                    & ( v4_pre_topc @ C @ A ) )
                 => ( ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) )
                    = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t51_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ X9 @ ( k9_subset_1 @ ( u1_struct_0 @ X9 ) @ X8 @ X10 ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ X9 ) @ ( k2_pre_topc @ X9 @ X8 ) @ ( k2_pre_topc @ X9 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t51_pre_topc])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v4_pre_topc @ X11 @ X12 )
      | ( ( k2_pre_topc @ X12 @ X11 )
        = X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['3','4','10'])).

thf('12',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v4_pre_topc @ X11 @ X12 )
      | ( ( k2_pre_topc @ X12 @ X11 )
        = X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_C )
      = sk_C )
    | ~ ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v4_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['12','18'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,
    ( ~ ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
      = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X3 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( r1_tarski @ X6 @ ( k2_pre_topc @ X7 @ X6 ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['21','28'])).

thf('30',plain,(
    ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
 != ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('32',plain,(
    ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
 != ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('34',plain,(
    ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
 != ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['29','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9FAV7LPGcR
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:27:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 38 iterations in 0.032s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(t34_tops_1, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48               ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 0.20/0.48                 ( ( k2_pre_topc @
% 0.20/0.48                     A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) =
% 0.20/0.48                   ( k9_subset_1 @
% 0.20/0.48                     ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.20/0.48                     ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( l1_pre_topc @ A ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48              ( ![C:$i]:
% 0.20/0.48                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48                  ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 0.20/0.48                    ( ( k2_pre_topc @
% 0.20/0.48                        A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) =
% 0.20/0.48                      ( k9_subset_1 @
% 0.20/0.48                        ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.20/0.48                        ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t34_tops_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t51_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48               ( r1_tarski @
% 0.20/0.48                 ( k2_pre_topc @
% 0.20/0.48                   A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 0.20/0.48                 ( k9_subset_1 @
% 0.20/0.48                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.20/0.48                   ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.48          | (r1_tarski @ 
% 0.20/0.48             (k2_pre_topc @ X9 @ (k9_subset_1 @ (u1_struct_0 @ X9) @ X8 @ X10)) @ 
% 0.20/0.48             (k9_subset_1 @ (u1_struct_0 @ X9) @ (k2_pre_topc @ X9 @ X8) @ 
% 0.20/0.48              (k2_pre_topc @ X9 @ X10)))
% 0.20/0.48          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.48          | ~ (l1_pre_topc @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [t51_pre_topc])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | (r1_tarski @ 
% 0.20/0.48             (k2_pre_topc @ sk_A @ 
% 0.20/0.48              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)) @ 
% 0.20/0.48             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48              (k2_pre_topc @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ X0))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t52_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.20/0.48             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.20/0.48               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.48          | ~ (v4_pre_topc @ X11 @ X12)
% 0.20/0.48          | ((k2_pre_topc @ X12 @ X11) = (X11))
% 0.20/0.48          | ~ (l1_pre_topc @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 0.20/0.48        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('9', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('10', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | (r1_tarski @ 
% 0.20/0.48             (k2_pre_topc @ sk_A @ 
% 0.20/0.48              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)) @ 
% 0.20/0.48             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48              (k2_pre_topc @ sk_A @ X0))))),
% 0.20/0.48      inference('demod', [status(thm)], ['3', '4', '10'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      ((r1_tarski @ 
% 0.20/0.48        (k2_pre_topc @ sk_A @ 
% 0.20/0.48         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 0.20/0.48        (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48         (k2_pre_topc @ sk_A @ sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['0', '11'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.48          | ~ (v4_pre_topc @ X11 @ X12)
% 0.20/0.48          | ((k2_pre_topc @ X12 @ X11) = (X11))
% 0.20/0.48          | ~ (l1_pre_topc @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.48        | ((k2_pre_topc @ sk_A @ sk_C) = (sk_C))
% 0.20/0.48        | ~ (v4_pre_topc @ sk_C @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('17', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('18', plain, (((k2_pre_topc @ sk_A @ sk_C) = (sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      ((r1_tarski @ 
% 0.20/0.48        (k2_pre_topc @ sk_A @ 
% 0.20/0.48         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 0.20/0.48        (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['12', '18'])).
% 0.20/0.48  thf(d10_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X0 : $i, X2 : $i]:
% 0.20/0.48         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      ((~ (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.20/0.48           (k2_pre_topc @ sk_A @ 
% 0.20/0.48            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)))
% 0.20/0.48        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.48            = (k2_pre_topc @ sk_A @ 
% 0.20/0.48               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_k9_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.48       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (k9_subset_1 @ X3 @ X4 @ X5) @ (k1_zfmisc_1 @ X3))
% 0.20/0.48          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X3)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ 
% 0.20/0.48          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf(t48_pre_topc, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.48          | (r1_tarski @ X6 @ (k2_pre_topc @ X7 @ X6))
% 0.20/0.48          | ~ (l1_pre_topc @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ 
% 0.20/0.48             (k2_pre_topc @ sk_A @ 
% 0.20/0.48              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.48  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ 
% 0.20/0.48          (k2_pre_topc @ sk_A @ 
% 0.20/0.48           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)))),
% 0.20/0.48      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 0.20/0.48         = (k2_pre_topc @ sk_A @ 
% 0.20/0.48            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)))),
% 0.20/0.48      inference('demod', [status(thm)], ['21', '28'])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (((k2_pre_topc @ sk_A @ 
% 0.20/0.48         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 0.20/0.48         != (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.48             (k2_pre_topc @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ sk_C)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('31', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.20/0.48      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (((k2_pre_topc @ sk_A @ 
% 0.20/0.48         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 0.20/0.48         != (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.20/0.48             (k2_pre_topc @ sk_A @ sk_C)))),
% 0.20/0.48      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.48  thf('33', plain, (((k2_pre_topc @ sk_A @ sk_C) = (sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (((k2_pre_topc @ sk_A @ 
% 0.20/0.48         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 0.20/0.48         != (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))),
% 0.20/0.48      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.48  thf('35', plain, ($false),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['29', '34'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
