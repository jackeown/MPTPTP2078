%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7qMuBOMpsd

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:27 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   50 (  66 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  361 ( 687 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tops_2_type,type,(
    v2_tops_2: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t25_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( v2_tops_2 @ B @ A )
               => ( v2_tops_2 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( ( v2_tops_2 @ B @ A )
                 => ( v2_tops_2 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_tops_2])).

thf('0',plain,(
    ~ ( v2_tops_2 @ ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C ) @ sk_A ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ( ( k7_subset_1 @ X34 @ X33 @ X35 )
        = ( k4_xboole_0 @ X33 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k6_subset_1 @ X31 @ X32 )
      = ( k4_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ( ( k7_subset_1 @ X34 @ X33 @ X35 )
        = ( k6_subset_1 @ X33 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( v2_tops_2 @ ( k6_subset_1 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X29: $i,X30: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X29 @ X30 ) @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_tarski @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( r1_tarski @ C @ B )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) ) )
      | ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) ) )
      | ~ ( r1_tarski @ X47 @ X45 )
      | ~ ( l1_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t3_tops_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('15',plain,(
    ! [X41: $i] :
      ( ( l1_struct_0 @ X41 )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('16',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf(t19_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( ( r1_tarski @ B @ C )
                  & ( v2_tops_2 @ C @ A ) )
               => ( v2_tops_2 @ B @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) ) )
      | ( v2_tops_2 @ X42 @ X43 )
      | ~ ( r1_tarski @ X42 @ X44 )
      | ~ ( v2_tops_2 @ X44 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t19_tops_2])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k6_subset_1 @ sk_B @ X0 ) @ X1 )
      | ( v2_tops_2 @ ( k6_subset_1 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( v2_tops_2 @ X1 @ sk_A )
      | ~ ( r1_tarski @ ( k6_subset_1 @ sk_B @ X0 ) @ X1 )
      | ( v2_tops_2 @ ( k6_subset_1 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_tops_2 @ ( k6_subset_1 @ sk_B @ X0 ) @ sk_A )
      | ~ ( r1_tarski @ ( k6_subset_1 @ sk_B @ X0 ) @ sk_B )
      | ~ ( v2_tops_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('25',plain,(
    v2_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( v2_tops_2 @ ( k6_subset_1 @ sk_B @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['6','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7qMuBOMpsd
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.63  % Solved by: fo/fo7.sh
% 0.42/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.63  % done 134 iterations in 0.128s
% 0.42/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.63  % SZS output start Refutation
% 0.42/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.63  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.42/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.63  thf(v2_tops_2_type, type, v2_tops_2: $i > $i > $o).
% 0.42/0.63  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.42/0.63  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.42/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.63  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.42/0.63  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.42/0.63  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.42/0.63  thf(t25_tops_2, conjecture,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( l1_pre_topc @ A ) =>
% 0.42/0.63       ( ![B:$i]:
% 0.42/0.63         ( ( m1_subset_1 @
% 0.42/0.63             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.42/0.63           ( ![C:$i]:
% 0.42/0.63             ( ( m1_subset_1 @
% 0.42/0.63                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.42/0.63               ( ( v2_tops_2 @ B @ A ) =>
% 0.42/0.63                 ( v2_tops_2 @
% 0.42/0.63                   ( k7_subset_1 @
% 0.42/0.63                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.42/0.63                   A ) ) ) ) ) ) ))).
% 0.42/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.63    (~( ![A:$i]:
% 0.42/0.63        ( ( l1_pre_topc @ A ) =>
% 0.42/0.63          ( ![B:$i]:
% 0.42/0.63            ( ( m1_subset_1 @
% 0.42/0.63                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.42/0.63              ( ![C:$i]:
% 0.42/0.63                ( ( m1_subset_1 @
% 0.42/0.63                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.42/0.63                  ( ( v2_tops_2 @ B @ A ) =>
% 0.42/0.63                    ( v2_tops_2 @
% 0.42/0.63                      ( k7_subset_1 @
% 0.42/0.63                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 0.42/0.63                      A ) ) ) ) ) ) ) )),
% 0.42/0.63    inference('cnf.neg', [status(esa)], [t25_tops_2])).
% 0.42/0.63  thf('0', plain,
% 0.42/0.63      (~ (v2_tops_2 @ 
% 0.42/0.63          (k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C) @ 
% 0.42/0.63          sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('1', plain,
% 0.42/0.63      ((m1_subset_1 @ sk_B @ 
% 0.42/0.63        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf(redefinition_k7_subset_1, axiom,
% 0.42/0.63    (![A:$i,B:$i,C:$i]:
% 0.42/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.63       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.42/0.63  thf('2', plain,
% 0.42/0.63      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.42/0.63         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.42/0.63          | ((k7_subset_1 @ X34 @ X33 @ X35) = (k4_xboole_0 @ X33 @ X35)))),
% 0.42/0.63      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.42/0.63  thf(redefinition_k6_subset_1, axiom,
% 0.42/0.63    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.42/0.63  thf('3', plain,
% 0.42/0.63      (![X31 : $i, X32 : $i]:
% 0.42/0.63         ((k6_subset_1 @ X31 @ X32) = (k4_xboole_0 @ X31 @ X32))),
% 0.42/0.63      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.42/0.63  thf('4', plain,
% 0.42/0.63      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.42/0.63         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.42/0.63          | ((k7_subset_1 @ X34 @ X33 @ X35) = (k6_subset_1 @ X33 @ X35)))),
% 0.42/0.63      inference('demod', [status(thm)], ['2', '3'])).
% 0.42/0.63  thf('5', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         ((k7_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ X0)
% 0.42/0.63           = (k6_subset_1 @ sk_B @ X0))),
% 0.42/0.63      inference('sup-', [status(thm)], ['1', '4'])).
% 0.42/0.63  thf('6', plain, (~ (v2_tops_2 @ (k6_subset_1 @ sk_B @ sk_C) @ sk_A)),
% 0.42/0.63      inference('demod', [status(thm)], ['0', '5'])).
% 0.42/0.63  thf('7', plain,
% 0.42/0.63      ((m1_subset_1 @ sk_B @ 
% 0.42/0.63        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf(dt_k6_subset_1, axiom,
% 0.42/0.63    (![A:$i,B:$i]:
% 0.42/0.63     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.42/0.63  thf('8', plain,
% 0.42/0.63      (![X29 : $i, X30 : $i]:
% 0.42/0.63         (m1_subset_1 @ (k6_subset_1 @ X29 @ X30) @ (k1_zfmisc_1 @ X29))),
% 0.42/0.63      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.42/0.63  thf(t3_subset, axiom,
% 0.42/0.63    (![A:$i,B:$i]:
% 0.42/0.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.42/0.63  thf('9', plain,
% 0.42/0.63      (![X38 : $i, X39 : $i]:
% 0.42/0.63         ((r1_tarski @ X38 @ X39) | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39)))),
% 0.42/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.63  thf('10', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 0.42/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.42/0.63  thf('11', plain,
% 0.42/0.63      ((m1_subset_1 @ sk_B @ 
% 0.42/0.63        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf(t3_tops_2, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( l1_struct_0 @ A ) =>
% 0.42/0.63       ( ![B:$i]:
% 0.42/0.63         ( ( m1_subset_1 @
% 0.42/0.63             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.42/0.63           ( ![C:$i]:
% 0.42/0.63             ( ( r1_tarski @ C @ B ) =>
% 0.42/0.63               ( m1_subset_1 @
% 0.42/0.63                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.42/0.63  thf('12', plain,
% 0.42/0.63      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.42/0.63         (~ (m1_subset_1 @ X45 @ 
% 0.42/0.63             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46))))
% 0.42/0.63          | (m1_subset_1 @ X47 @ 
% 0.42/0.63             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46))))
% 0.42/0.63          | ~ (r1_tarski @ X47 @ X45)
% 0.42/0.63          | ~ (l1_struct_0 @ X46))),
% 0.42/0.63      inference('cnf', [status(esa)], [t3_tops_2])).
% 0.42/0.63  thf('13', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (~ (l1_struct_0 @ sk_A)
% 0.42/0.63          | ~ (r1_tarski @ X0 @ sk_B)
% 0.42/0.63          | (m1_subset_1 @ X0 @ 
% 0.42/0.63             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.42/0.63      inference('sup-', [status(thm)], ['11', '12'])).
% 0.42/0.63  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf(dt_l1_pre_topc, axiom,
% 0.42/0.63    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.42/0.63  thf('15', plain,
% 0.42/0.63      (![X41 : $i]: ((l1_struct_0 @ X41) | ~ (l1_pre_topc @ X41))),
% 0.42/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.42/0.63  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 0.42/0.63      inference('sup-', [status(thm)], ['14', '15'])).
% 0.42/0.63  thf('17', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (~ (r1_tarski @ X0 @ sk_B)
% 0.42/0.63          | (m1_subset_1 @ X0 @ 
% 0.42/0.63             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.42/0.63      inference('demod', [status(thm)], ['13', '16'])).
% 0.42/0.63  thf('18', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         (m1_subset_1 @ (k6_subset_1 @ sk_B @ X0) @ 
% 0.42/0.63          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.42/0.63      inference('sup-', [status(thm)], ['10', '17'])).
% 0.42/0.63  thf(t19_tops_2, axiom,
% 0.42/0.63    (![A:$i]:
% 0.42/0.63     ( ( l1_pre_topc @ A ) =>
% 0.42/0.63       ( ![B:$i]:
% 0.42/0.63         ( ( m1_subset_1 @
% 0.42/0.63             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.42/0.63           ( ![C:$i]:
% 0.42/0.63             ( ( m1_subset_1 @
% 0.42/0.63                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.42/0.63               ( ( ( r1_tarski @ B @ C ) & ( v2_tops_2 @ C @ A ) ) =>
% 0.42/0.63                 ( v2_tops_2 @ B @ A ) ) ) ) ) ) ))).
% 0.42/0.63  thf('19', plain,
% 0.42/0.63      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.42/0.63         (~ (m1_subset_1 @ X42 @ 
% 0.42/0.63             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43))))
% 0.42/0.63          | (v2_tops_2 @ X42 @ X43)
% 0.42/0.63          | ~ (r1_tarski @ X42 @ X44)
% 0.42/0.63          | ~ (v2_tops_2 @ X44 @ X43)
% 0.42/0.63          | ~ (m1_subset_1 @ X44 @ 
% 0.42/0.63               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43))))
% 0.42/0.63          | ~ (l1_pre_topc @ X43))),
% 0.42/0.63      inference('cnf', [status(esa)], [t19_tops_2])).
% 0.42/0.63  thf('20', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         (~ (l1_pre_topc @ sk_A)
% 0.42/0.63          | ~ (m1_subset_1 @ X1 @ 
% 0.42/0.63               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.42/0.63          | ~ (v2_tops_2 @ X1 @ sk_A)
% 0.42/0.63          | ~ (r1_tarski @ (k6_subset_1 @ sk_B @ X0) @ X1)
% 0.42/0.63          | (v2_tops_2 @ (k6_subset_1 @ sk_B @ X0) @ sk_A))),
% 0.42/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.42/0.63  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('22', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]:
% 0.42/0.63         (~ (m1_subset_1 @ X1 @ 
% 0.42/0.63             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.42/0.63          | ~ (v2_tops_2 @ X1 @ sk_A)
% 0.42/0.63          | ~ (r1_tarski @ (k6_subset_1 @ sk_B @ X0) @ X1)
% 0.42/0.63          | (v2_tops_2 @ (k6_subset_1 @ sk_B @ X0) @ sk_A))),
% 0.42/0.63      inference('demod', [status(thm)], ['20', '21'])).
% 0.42/0.63  thf('23', plain,
% 0.42/0.63      (![X0 : $i]:
% 0.42/0.63         ((v2_tops_2 @ (k6_subset_1 @ sk_B @ X0) @ sk_A)
% 0.42/0.63          | ~ (r1_tarski @ (k6_subset_1 @ sk_B @ X0) @ sk_B)
% 0.42/0.63          | ~ (v2_tops_2 @ sk_B @ sk_A))),
% 0.42/0.63      inference('sup-', [status(thm)], ['7', '22'])).
% 0.42/0.63  thf('24', plain,
% 0.42/0.63      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X0)),
% 0.42/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.42/0.63  thf('25', plain, ((v2_tops_2 @ sk_B @ sk_A)),
% 0.42/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.63  thf('26', plain,
% 0.42/0.63      (![X0 : $i]: (v2_tops_2 @ (k6_subset_1 @ sk_B @ X0) @ sk_A)),
% 0.42/0.63      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.42/0.63  thf('27', plain, ($false), inference('demod', [status(thm)], ['6', '26'])).
% 0.42/0.63  
% 0.42/0.63  % SZS output end Refutation
% 0.42/0.63  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
