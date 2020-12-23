%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HnFWMZonEn

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:17 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   57 (  80 expanded)
%              Number of leaves         :   20 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  364 ( 875 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t19_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( ( r1_tarski @ B @ C )
                  & ( v2_tops_2 @ C @ A ) )
               => ( v2_tops_2 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( ( ( r1_tarski @ B @ C )
                    & ( v2_tops_2 @ C @ A ) )
                 => ( v2_tops_2 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_tops_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tops_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v4_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v4_pre_topc @ ( sk_C @ X11 @ X12 ) @ X12 )
      | ( v2_tops_2 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_2 @ sk_B @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ~ ( v4_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ~ ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( v4_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) )
      | ( r2_hidden @ ( sk_C @ X11 @ X12 ) @ X11 )
      | ( v2_tops_2 @ X11 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v2_tops_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v2_tops_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['12','13'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('15',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X5 ) @ X7 )
      | ~ ( r2_hidden @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('16',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_C @ sk_B @ sk_A ) ) @ sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('18',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_C @ sk_B @ sk_A ) ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ sk_B @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_C @ sk_B @ sk_A ) ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['7','20'])).

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_tarski @ ( k1_tarski @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('23',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v2_tops_2 @ X11 @ X12 )
      | ~ ( r2_hidden @ X13 @ X11 )
      | ( v4_pre_topc @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_2])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( v2_tops_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_tops_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('31',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['29','32'])).

thf('34',plain,(
    v4_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['23','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['6','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HnFWMZonEn
% 0.14/0.36  % Computer   : n003.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 16:31:27 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 31 iterations in 0.015s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.47  thf(v2_tops_2_type, type, v2_tops_2: $i > $i > $o).
% 0.22/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.47  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.22/0.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.47  thf(t19_tops_2, conjecture,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( l1_pre_topc @ A ) =>
% 0.22/0.47       ( ![B:$i]:
% 0.22/0.47         ( ( m1_subset_1 @
% 0.22/0.47             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.47           ( ![C:$i]:
% 0.22/0.47             ( ( m1_subset_1 @
% 0.22/0.47                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.47               ( ( ( r1_tarski @ B @ C ) & ( v2_tops_2 @ C @ A ) ) =>
% 0.22/0.47                 ( v2_tops_2 @ B @ A ) ) ) ) ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i]:
% 0.22/0.47        ( ( l1_pre_topc @ A ) =>
% 0.22/0.47          ( ![B:$i]:
% 0.22/0.47            ( ( m1_subset_1 @
% 0.22/0.47                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.47              ( ![C:$i]:
% 0.22/0.47                ( ( m1_subset_1 @
% 0.22/0.47                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.47                  ( ( ( r1_tarski @ B @ C ) & ( v2_tops_2 @ C @ A ) ) =>
% 0.22/0.47                    ( v2_tops_2 @ B @ A ) ) ) ) ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t19_tops_2])).
% 0.22/0.47  thf('0', plain,
% 0.22/0.47      ((m1_subset_1 @ sk_B @ 
% 0.22/0.47        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(d2_tops_2, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( l1_pre_topc @ A ) =>
% 0.22/0.47       ( ![B:$i]:
% 0.22/0.47         ( ( m1_subset_1 @
% 0.22/0.47             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.47           ( ( v2_tops_2 @ B @ A ) <=>
% 0.22/0.47             ( ![C:$i]:
% 0.22/0.47               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.47                 ( ( r2_hidden @ C @ B ) => ( v4_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      (![X11 : $i, X12 : $i]:
% 0.22/0.47         (~ (m1_subset_1 @ X11 @ 
% 0.22/0.47             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12))))
% 0.22/0.47          | ~ (v4_pre_topc @ (sk_C @ X11 @ X12) @ X12)
% 0.22/0.47          | (v2_tops_2 @ X11 @ X12)
% 0.22/0.47          | ~ (l1_pre_topc @ X12))),
% 0.22/0.47      inference('cnf', [status(esa)], [d2_tops_2])).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.47        | (v2_tops_2 @ sk_B @ sk_A)
% 0.22/0.47        | ~ (v4_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.22/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.47  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('4', plain,
% 0.22/0.47      (((v2_tops_2 @ sk_B @ sk_A)
% 0.22/0.47        | ~ (v4_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.22/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.47  thf('5', plain, (~ (v2_tops_2 @ sk_B @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('6', plain, (~ (v4_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.22/0.47      inference('clc', [status(thm)], ['4', '5'])).
% 0.22/0.47  thf('7', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('8', plain,
% 0.22/0.47      ((m1_subset_1 @ sk_B @ 
% 0.22/0.47        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('9', plain,
% 0.22/0.47      (![X11 : $i, X12 : $i]:
% 0.22/0.47         (~ (m1_subset_1 @ X11 @ 
% 0.22/0.47             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12))))
% 0.22/0.47          | (r2_hidden @ (sk_C @ X11 @ X12) @ X11)
% 0.22/0.47          | (v2_tops_2 @ X11 @ X12)
% 0.22/0.47          | ~ (l1_pre_topc @ X12))),
% 0.22/0.47      inference('cnf', [status(esa)], [d2_tops_2])).
% 0.22/0.47  thf('10', plain,
% 0.22/0.47      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.47        | (v2_tops_2 @ sk_B @ sk_A)
% 0.22/0.47        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.22/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.47  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('12', plain,
% 0.22/0.47      (((v2_tops_2 @ sk_B @ sk_A) | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.22/0.47      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.47  thf('13', plain, (~ (v2_tops_2 @ sk_B @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('14', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.22/0.47      inference('clc', [status(thm)], ['12', '13'])).
% 0.22/0.47  thf(l1_zfmisc_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.22/0.47  thf('15', plain,
% 0.22/0.47      (![X5 : $i, X7 : $i]:
% 0.22/0.47         ((r1_tarski @ (k1_tarski @ X5) @ X7) | ~ (r2_hidden @ X5 @ X7))),
% 0.22/0.47      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.22/0.47  thf('16', plain, ((r1_tarski @ (k1_tarski @ (sk_C @ sk_B @ sk_A)) @ sk_B)),
% 0.22/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.47  thf(t12_xboole_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.22/0.47  thf('17', plain,
% 0.22/0.47      (![X3 : $i, X4 : $i]:
% 0.22/0.47         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.22/0.47      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.22/0.47  thf('18', plain,
% 0.22/0.47      (((k2_xboole_0 @ (k1_tarski @ (sk_C @ sk_B @ sk_A)) @ sk_B) = (sk_B))),
% 0.22/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.47  thf(t11_xboole_1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.22/0.47  thf('19', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.47         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.22/0.47      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.22/0.47  thf('20', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (r1_tarski @ sk_B @ X0)
% 0.22/0.47          | (r1_tarski @ (k1_tarski @ (sk_C @ sk_B @ sk_A)) @ X0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.47  thf('21', plain, ((r1_tarski @ (k1_tarski @ (sk_C @ sk_B @ sk_A)) @ sk_C_1)),
% 0.22/0.47      inference('sup-', [status(thm)], ['7', '20'])).
% 0.22/0.47  thf('22', plain,
% 0.22/0.47      (![X5 : $i, X6 : $i]:
% 0.22/0.47         ((r2_hidden @ X5 @ X6) | ~ (r1_tarski @ (k1_tarski @ X5) @ X6))),
% 0.22/0.47      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.22/0.47  thf('23', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_C_1)),
% 0.22/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.47  thf('24', plain,
% 0.22/0.47      ((m1_subset_1 @ sk_C_1 @ 
% 0.22/0.47        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('25', plain,
% 0.22/0.47      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.47         (~ (m1_subset_1 @ X11 @ 
% 0.22/0.47             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12))))
% 0.22/0.47          | ~ (v2_tops_2 @ X11 @ X12)
% 0.22/0.47          | ~ (r2_hidden @ X13 @ X11)
% 0.22/0.47          | (v4_pre_topc @ X13 @ X12)
% 0.22/0.47          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.22/0.47          | ~ (l1_pre_topc @ X12))),
% 0.22/0.47      inference('cnf', [status(esa)], [d2_tops_2])).
% 0.22/0.47  thf('26', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (l1_pre_topc @ sk_A)
% 0.22/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.47          | (v4_pre_topc @ X0 @ sk_A)
% 0.22/0.47          | ~ (r2_hidden @ X0 @ sk_C_1)
% 0.22/0.47          | ~ (v2_tops_2 @ sk_C_1 @ sk_A))),
% 0.22/0.47      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.47  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('28', plain, ((v2_tops_2 @ sk_C_1 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('29', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.47          | (v4_pre_topc @ X0 @ sk_A)
% 0.22/0.47          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.22/0.47      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.22/0.47  thf('30', plain,
% 0.22/0.47      ((m1_subset_1 @ sk_C_1 @ 
% 0.22/0.47        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(t4_subset, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.22/0.47       ( m1_subset_1 @ A @ C ) ))).
% 0.22/0.47  thf('31', plain,
% 0.22/0.47      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X8 @ X9)
% 0.22/0.47          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.22/0.47          | (m1_subset_1 @ X8 @ X10))),
% 0.22/0.47      inference('cnf', [status(esa)], [t4_subset])).
% 0.22/0.47  thf('32', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.47          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.22/0.47      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.47  thf('33', plain,
% 0.22/0.47      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_C_1) | (v4_pre_topc @ X0 @ sk_A))),
% 0.22/0.47      inference('clc', [status(thm)], ['29', '32'])).
% 0.22/0.47  thf('34', plain, ((v4_pre_topc @ (sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.22/0.47      inference('sup-', [status(thm)], ['23', '33'])).
% 0.22/0.47  thf('35', plain, ($false), inference('demod', [status(thm)], ['6', '34'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
