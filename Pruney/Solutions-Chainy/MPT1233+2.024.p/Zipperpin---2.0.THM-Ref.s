%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KwUw9wV32S

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   77 (  96 expanded)
%              Number of leaves         :   31 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  470 ( 612 expanded)
%              Number of equality atoms :   39 (  51 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X14: $i] :
      ( ( ( k2_struct_0 @ X14 )
        = ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v4_pre_topc @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('5',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

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

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v4_pre_topc @ X16 @ X17 )
      | ( ( k2_pre_topc @ X17 @ X16 )
        = X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('12',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('13',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('14',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k1_tops_1 @ X19 @ X18 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k2_pre_topc @ X19 @ ( k3_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 ) ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['16','19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','23'])).

thf('25',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('28',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','31'])).

thf(t43_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
          = ( k2_struct_0 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_tops_1])).

thf('33',plain,(
    ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('38',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('39',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ( u1_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['34','35','36','39'])).

thf('41',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','40'])).

thf('42',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['37','38'])).

thf('43',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference(simplify,[status(thm)],['43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KwUw9wV32S
% 0.14/0.36  % Computer   : n004.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 10:53:39 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 133 iterations in 0.045s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.22/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.52  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.52  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.22/0.52  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.22/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(d3_struct_0, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      (![X14 : $i]:
% 0.22/0.52         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X14 : $i]:
% 0.22/0.52         (((k2_struct_0 @ X14) = (u1_struct_0 @ X14)) | ~ (l1_struct_0 @ X14))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.52  thf(t4_subset_1, axiom,
% 0.22/0.52    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.22/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.52  thf(cc2_pre_topc, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X12 : $i, X13 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.22/0.52          | (v4_pre_topc @ X12 @ X13)
% 0.22/0.52          | ~ (v1_xboole_0 @ X12)
% 0.22/0.52          | ~ (l1_pre_topc @ X13)
% 0.22/0.52          | ~ (v2_pre_topc @ X13))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.52          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.52  thf('5', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.22/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.52  thf(t52_pre_topc, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_pre_topc @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.22/0.52             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.22/0.52               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X16 : $i, X17 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.22/0.52          | ~ (v4_pre_topc @ X16 @ X17)
% 0.22/0.52          | ((k2_pre_topc @ X17 @ X16) = (X16))
% 0.22/0.52          | ~ (l1_pre_topc @ X17))),
% 0.22/0.52      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (l1_pre_topc @ X0)
% 0.22/0.52          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.22/0.52          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.22/0.52          | ~ (l1_pre_topc @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['6', '9'])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['10'])).
% 0.22/0.52  thf(dt_k2_subset_1, axiom,
% 0.22/0.52    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (![X7 : $i]: (m1_subset_1 @ (k2_subset_1 @ X7) @ (k1_zfmisc_1 @ X7))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.22/0.52  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.22/0.52  thf('13', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.22/0.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.52  thf('14', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.22/0.52      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf(d1_tops_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_pre_topc @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( ( k1_tops_1 @ A @ B ) =
% 0.22/0.52             ( k3_subset_1 @
% 0.22/0.52               ( u1_struct_0 @ A ) @ 
% 0.22/0.52               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X18 : $i, X19 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.22/0.52          | ((k1_tops_1 @ X19 @ X18)
% 0.22/0.52              = (k3_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.22/0.52                 (k2_pre_topc @ X19 @ (k3_subset_1 @ (u1_struct_0 @ X19) @ X18))))
% 0.22/0.52          | ~ (l1_pre_topc @ X19))),
% 0.22/0.52      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (l1_pre_topc @ X0)
% 0.22/0.52          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.22/0.52              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.52                 (k2_pre_topc @ X0 @ 
% 0.22/0.52                  (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.52  thf('17', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.22/0.52      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf(d5_subset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X5 : $i, X6 : $i]:
% 0.22/0.52         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 0.22/0.52          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf(t1_boole, axiom,
% 0.22/0.52    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.52  thf('20', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.52  thf(t46_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (![X2 : $i, X3 : $i]:
% 0.22/0.52         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X3)) = (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.22/0.52  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['20', '21'])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (l1_pre_topc @ X0)
% 0.22/0.52          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.22/0.52              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.52                 (k2_pre_topc @ X0 @ k1_xboole_0))))),
% 0.22/0.52      inference('demod', [status(thm)], ['16', '19', '22'])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.22/0.52            = (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0))
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['11', '23'])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.22/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X5 : $i, X6 : $i]:
% 0.22/0.52         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 0.22/0.52          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.22/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.52  thf(t3_boole, axiom,
% 0.22/0.52    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.52  thf('28', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.52  thf('29', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k1_tops_1 @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['24', '29'])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['30'])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k1_tops_1 @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.22/0.52          | ~ (l1_struct_0 @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['1', '31'])).
% 0.22/0.52  thf(t43_tops_1, conjecture,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i]:
% 0.22/0.52        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52          ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t43_tops_1])).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) != (k2_struct_0 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      ((((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.22/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52        | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.52  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(dt_l1_pre_topc, axiom,
% 0.22/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.52  thf('39', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.52  thf('40', plain, (((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['34', '35', '36', '39'])).
% 0.22/0.52  thf('41', plain,
% 0.22/0.52      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '40'])).
% 0.22/0.52  thf('42', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.52  thf('43', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['41', '42'])).
% 0.22/0.52  thf('44', plain, ($false), inference('simplify', [status(thm)], ['43'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
