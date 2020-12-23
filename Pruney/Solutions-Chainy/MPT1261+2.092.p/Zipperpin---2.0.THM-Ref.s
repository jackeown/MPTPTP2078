%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5KQuvtPL7F

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:51 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :  219 (2113 expanded)
%              Number of leaves         :   44 ( 662 expanded)
%              Depth                    :   23
%              Number of atoms          : 1947 (24210 expanded)
%              Number of equality atoms :  141 (1622 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t77_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_tops_1])).

thf('0',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('3',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X58 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X58 @ X57 ) @ X57 )
      | ~ ( v4_pre_topc @ X57 @ X58 )
      | ~ ( l1_pre_topc @ X58 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('13',plain,
    ( ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('16',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','17'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('21',plain,(
    ! [X40: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','29'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['20','30','31'])).

thf('33',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('37',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('39',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X43: $i,X45: $i] :
      ( ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X45 ) )
      | ~ ( r1_tarski @ X43 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('42',plain,(
    ! [X30: $i,X31: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('43',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('44',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( ( k2_pre_topc @ X56 @ X55 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X56 ) @ X55 @ ( k2_tops_1 @ X56 @ X55 ) ) )
      | ~ ( l1_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('49',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('50',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('52',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('54',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('55',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('57',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X33 @ ( k3_subset_1 @ X33 @ X32 ) )
        = X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('58',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( sk_B
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('60',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['52','59'])).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('62',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('66',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['56','57'])).

thf('68',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('69',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('71',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['67','68'])).

thf('72',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('73',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['67','68'])).

thf('74',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','66','69','70','71','72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('76',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ( ( k7_subset_1 @ X38 @ X37 @ X39 )
        = ( k4_xboole_0 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('79',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('81',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X43: $i,X44: $i] :
      ( ( r1_tarski @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('85',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('86',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X43: $i,X45: $i] :
      ( ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X45 ) )
      | ~ ( r1_tarski @ X43 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('92',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['79','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('95',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X35 ) )
      | ( ( k4_subset_1 @ X35 @ X34 @ X36 )
        = ( k2_xboole_0 @ X34 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('99',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('100',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['98','103'])).

thf('105',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['97','104'])).

thf('106',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['74','105'])).

thf('107',plain,(
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

thf('108',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ~ ( v2_pre_topc @ X50 )
      | ( ( k2_pre_topc @ X50 @ X49 )
       != X49 )
      | ( v4_pre_topc @ X49 @ X50 )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('109',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['106','112'])).

thf('114',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['33'])).

thf('116',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('118',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['34','116','117'])).

thf('119',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['32','118'])).

thf('120',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('121',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['122','123','124','125'])).

thf('127',plain,
    ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = sk_B ),
    inference('sup+',[status(thm)],['119','126'])).

thf('128',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('129',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ( ( k1_tops_1 @ X60 @ X59 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X60 ) @ X59 @ ( k2_tops_1 @ X60 @ X59 ) ) )
      | ~ ( l1_pre_topc @ X60 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('130',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('134',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('136',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['127','134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('138',plain,(
    ! [X43: $i,X45: $i] :
      ( ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X45 ) )
      | ~ ( r1_tarski @ X43 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X33 @ ( k3_subset_1 @ X33 @ X32 ) )
        = X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,
    ( ( k3_subset_1 @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['136','141'])).

thf('143',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['127','134','135'])).

thf('144',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['20','30','31'])).

thf('145',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('146',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('147',plain,(
    ! [X43: $i,X45: $i] :
      ( ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X45 ) )
      | ~ ( r1_tarski @ X43 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['145','148'])).

thf('150',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['144','151'])).

thf('153',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['20','30','31'])).

thf('154',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('155',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('156',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['34','116','117'])).

thf('157',plain,
    ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['155','156'])).

thf('158',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['142','143','157'])).

thf('159',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['33'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('161',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('162',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X52 @ X51 ) @ X51 )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('163',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X43: $i,X45: $i] :
      ( ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X45 ) )
      | ~ ( r1_tarski @ X43 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('167',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('169',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['159','160','169'])).

thf('171',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['34','116'])).

thf('172',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['170','171'])).

thf('173',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['158','172'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5KQuvtPL7F
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:54:18 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.22/1.42  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.22/1.42  % Solved by: fo/fo7.sh
% 1.22/1.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.22/1.42  % done 3345 iterations in 0.943s
% 1.22/1.42  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.22/1.42  % SZS output start Refutation
% 1.22/1.42  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.22/1.42  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.22/1.42  thf(sk_B_type, type, sk_B: $i).
% 1.22/1.42  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.22/1.42  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.22/1.42  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.22/1.42  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.22/1.42  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.22/1.42  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.22/1.42  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.22/1.42  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.22/1.42  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.22/1.42  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.22/1.42  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.22/1.42  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.22/1.42  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.22/1.42  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.22/1.42  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.22/1.42  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.22/1.42  thf(sk_A_type, type, sk_A: $i).
% 1.22/1.42  thf(t77_tops_1, conjecture,
% 1.22/1.42    (![A:$i]:
% 1.22/1.42     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.22/1.42       ( ![B:$i]:
% 1.22/1.42         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.22/1.42           ( ( v4_pre_topc @ B @ A ) <=>
% 1.22/1.42             ( ( k2_tops_1 @ A @ B ) =
% 1.22/1.42               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.22/1.42  thf(zf_stmt_0, negated_conjecture,
% 1.22/1.42    (~( ![A:$i]:
% 1.22/1.42        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.22/1.42          ( ![B:$i]:
% 1.22/1.42            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.22/1.42              ( ( v4_pre_topc @ B @ A ) <=>
% 1.22/1.42                ( ( k2_tops_1 @ A @ B ) =
% 1.22/1.42                  ( k7_subset_1 @
% 1.22/1.42                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.22/1.42    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 1.22/1.42  thf('0', plain,
% 1.22/1.42      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.42          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.22/1.42             (k1_tops_1 @ sk_A @ sk_B)))
% 1.22/1.42        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.22/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.42  thf('1', plain,
% 1.22/1.42      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.22/1.42      inference('split', [status(esa)], ['0'])).
% 1.22/1.42  thf('2', plain,
% 1.22/1.42      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.22/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.42  thf(t69_tops_1, axiom,
% 1.22/1.42    (![A:$i]:
% 1.22/1.42     ( ( l1_pre_topc @ A ) =>
% 1.22/1.42       ( ![B:$i]:
% 1.22/1.42         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.22/1.42           ( ( v4_pre_topc @ B @ A ) =>
% 1.22/1.42             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 1.22/1.42  thf('3', plain,
% 1.22/1.42      (![X57 : $i, X58 : $i]:
% 1.22/1.42         (~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X58)))
% 1.22/1.42          | (r1_tarski @ (k2_tops_1 @ X58 @ X57) @ X57)
% 1.22/1.42          | ~ (v4_pre_topc @ X57 @ X58)
% 1.22/1.42          | ~ (l1_pre_topc @ X58))),
% 1.22/1.42      inference('cnf', [status(esa)], [t69_tops_1])).
% 1.22/1.42  thf('4', plain,
% 1.22/1.42      ((~ (l1_pre_topc @ sk_A)
% 1.22/1.42        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 1.22/1.42        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.22/1.42      inference('sup-', [status(thm)], ['2', '3'])).
% 1.22/1.42  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.22/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.42  thf('6', plain,
% 1.22/1.42      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 1.22/1.42        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.22/1.42      inference('demod', [status(thm)], ['4', '5'])).
% 1.22/1.42  thf('7', plain,
% 1.22/1.42      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.22/1.42         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.22/1.42      inference('sup-', [status(thm)], ['1', '6'])).
% 1.22/1.42  thf(t1_boole, axiom,
% 1.22/1.42    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.22/1.42  thf('8', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 1.22/1.42      inference('cnf', [status(esa)], [t1_boole])).
% 1.22/1.42  thf(t43_xboole_1, axiom,
% 1.22/1.42    (![A:$i,B:$i,C:$i]:
% 1.22/1.42     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.22/1.42       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.22/1.42  thf('9', plain,
% 1.22/1.42      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.22/1.42         ((r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 1.22/1.42          | ~ (r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 1.22/1.42      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.22/1.42  thf('10', plain,
% 1.22/1.42      (![X0 : $i, X1 : $i]:
% 1.22/1.42         (~ (r1_tarski @ X1 @ X0)
% 1.22/1.42          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 1.22/1.42      inference('sup-', [status(thm)], ['8', '9'])).
% 1.22/1.42  thf('11', plain,
% 1.22/1.42      (((r1_tarski @ (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ 
% 1.22/1.42         k1_xboole_0)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.22/1.42      inference('sup-', [status(thm)], ['7', '10'])).
% 1.22/1.42  thf(t12_xboole_1, axiom,
% 1.22/1.42    (![A:$i,B:$i]:
% 1.22/1.42     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.22/1.42  thf('12', plain,
% 1.22/1.42      (![X6 : $i, X7 : $i]:
% 1.22/1.42         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 1.22/1.42      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.22/1.42  thf('13', plain,
% 1.22/1.42      ((((k2_xboole_0 @ (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ 
% 1.22/1.42          k1_xboole_0) = (k1_xboole_0)))
% 1.22/1.42         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.22/1.42      inference('sup-', [status(thm)], ['11', '12'])).
% 1.22/1.42  thf(commutativity_k2_xboole_0, axiom,
% 1.22/1.42    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.22/1.42  thf('14', plain,
% 1.22/1.42      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.22/1.42      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.22/1.42  thf('15', plain,
% 1.22/1.42      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.22/1.42      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.22/1.42  thf('16', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 1.22/1.42      inference('cnf', [status(esa)], [t1_boole])).
% 1.22/1.42  thf('17', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.22/1.42      inference('sup+', [status(thm)], ['15', '16'])).
% 1.22/1.42  thf('18', plain,
% 1.22/1.42      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 1.22/1.42         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.22/1.42      inference('demod', [status(thm)], ['13', '14', '17'])).
% 1.22/1.42  thf(t48_xboole_1, axiom,
% 1.22/1.42    (![A:$i,B:$i]:
% 1.22/1.42     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.22/1.42  thf('19', plain,
% 1.22/1.42      (![X22 : $i, X23 : $i]:
% 1.22/1.42         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 1.22/1.42           = (k3_xboole_0 @ X22 @ X23))),
% 1.22/1.42      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.22/1.42  thf('20', plain,
% 1.22/1.42      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 1.22/1.42          = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 1.22/1.42         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.22/1.42      inference('sup+', [status(thm)], ['18', '19'])).
% 1.22/1.42  thf(t4_subset_1, axiom,
% 1.22/1.42    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.22/1.42  thf('21', plain,
% 1.22/1.42      (![X40 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X40))),
% 1.22/1.42      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.22/1.42  thf(d5_subset_1, axiom,
% 1.22/1.42    (![A:$i,B:$i]:
% 1.22/1.42     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.22/1.42       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.22/1.42  thf('22', plain,
% 1.22/1.42      (![X27 : $i, X28 : $i]:
% 1.22/1.42         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 1.22/1.42          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 1.22/1.42      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.22/1.42  thf('23', plain,
% 1.22/1.42      (![X0 : $i]:
% 1.22/1.42         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.22/1.42      inference('sup-', [status(thm)], ['21', '22'])).
% 1.22/1.42  thf('24', plain,
% 1.22/1.42      (![X0 : $i]:
% 1.22/1.42         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.22/1.42      inference('sup-', [status(thm)], ['21', '22'])).
% 1.22/1.42  thf(t39_xboole_1, axiom,
% 1.22/1.42    (![A:$i,B:$i]:
% 1.22/1.42     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.22/1.42  thf('25', plain,
% 1.22/1.42      (![X14 : $i, X15 : $i]:
% 1.22/1.42         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 1.22/1.42           = (k2_xboole_0 @ X14 @ X15))),
% 1.22/1.42      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.22/1.42  thf('26', plain,
% 1.22/1.42      (![X0 : $i]:
% 1.22/1.42         ((k2_xboole_0 @ k1_xboole_0 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 1.22/1.42           = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 1.22/1.42      inference('sup+', [status(thm)], ['24', '25'])).
% 1.22/1.42  thf('27', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.22/1.42      inference('sup+', [status(thm)], ['15', '16'])).
% 1.22/1.42  thf('28', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.22/1.42      inference('sup+', [status(thm)], ['15', '16'])).
% 1.22/1.42  thf('29', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 1.22/1.42      inference('demod', [status(thm)], ['26', '27', '28'])).
% 1.22/1.42  thf('30', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.22/1.42      inference('demod', [status(thm)], ['23', '29'])).
% 1.22/1.42  thf(commutativity_k3_xboole_0, axiom,
% 1.22/1.42    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.22/1.42  thf('31', plain,
% 1.22/1.42      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.22/1.42      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.22/1.42  thf('32', plain,
% 1.22/1.42      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.42          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.22/1.42         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.22/1.42      inference('demod', [status(thm)], ['20', '30', '31'])).
% 1.22/1.42  thf('33', plain,
% 1.22/1.42      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.42          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.22/1.42              (k1_tops_1 @ sk_A @ sk_B)))
% 1.22/1.42        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.22/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.42  thf('34', plain,
% 1.22/1.42      (~
% 1.22/1.42       (((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.42          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.22/1.42             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.22/1.42       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.22/1.42      inference('split', [status(esa)], ['33'])).
% 1.22/1.42  thf('35', plain,
% 1.22/1.42      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.22/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.42  thf('36', plain,
% 1.22/1.42      (![X27 : $i, X28 : $i]:
% 1.22/1.42         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 1.22/1.42          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 1.22/1.42      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.22/1.42  thf('37', plain,
% 1.22/1.42      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.22/1.42         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.22/1.42      inference('sup-', [status(thm)], ['35', '36'])).
% 1.22/1.42  thf(t36_xboole_1, axiom,
% 1.22/1.42    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.22/1.42  thf('38', plain,
% 1.22/1.42      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 1.22/1.42      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.22/1.42  thf('39', plain,
% 1.22/1.42      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.22/1.42        (u1_struct_0 @ sk_A))),
% 1.22/1.42      inference('sup+', [status(thm)], ['37', '38'])).
% 1.22/1.42  thf(t3_subset, axiom,
% 1.22/1.42    (![A:$i,B:$i]:
% 1.22/1.42     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.22/1.42  thf('40', plain,
% 1.22/1.42      (![X43 : $i, X45 : $i]:
% 1.22/1.42         ((m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X45)) | ~ (r1_tarski @ X43 @ X45))),
% 1.22/1.42      inference('cnf', [status(esa)], [t3_subset])).
% 1.22/1.42  thf('41', plain,
% 1.22/1.42      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.22/1.42        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.22/1.42      inference('sup-', [status(thm)], ['39', '40'])).
% 1.22/1.42  thf(dt_k3_subset_1, axiom,
% 1.22/1.42    (![A:$i,B:$i]:
% 1.22/1.42     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.22/1.42       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.22/1.42  thf('42', plain,
% 1.22/1.42      (![X30 : $i, X31 : $i]:
% 1.22/1.42         ((m1_subset_1 @ (k3_subset_1 @ X30 @ X31) @ (k1_zfmisc_1 @ X30))
% 1.22/1.42          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 1.22/1.42      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.22/1.42  thf('43', plain,
% 1.22/1.42      ((m1_subset_1 @ 
% 1.22/1.42        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.42         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.22/1.42        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.22/1.42      inference('sup-', [status(thm)], ['41', '42'])).
% 1.22/1.42  thf(t65_tops_1, axiom,
% 1.22/1.42    (![A:$i]:
% 1.22/1.42     ( ( l1_pre_topc @ A ) =>
% 1.22/1.42       ( ![B:$i]:
% 1.22/1.42         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.22/1.42           ( ( k2_pre_topc @ A @ B ) =
% 1.22/1.42             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.22/1.42  thf('44', plain,
% 1.22/1.42      (![X55 : $i, X56 : $i]:
% 1.22/1.42         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 1.22/1.42          | ((k2_pre_topc @ X56 @ X55)
% 1.22/1.42              = (k4_subset_1 @ (u1_struct_0 @ X56) @ X55 @ 
% 1.22/1.42                 (k2_tops_1 @ X56 @ X55)))
% 1.22/1.42          | ~ (l1_pre_topc @ X56))),
% 1.22/1.42      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.22/1.42  thf('45', plain,
% 1.22/1.42      ((~ (l1_pre_topc @ sk_A)
% 1.22/1.42        | ((k2_pre_topc @ sk_A @ 
% 1.22/1.42            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.42             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.22/1.42            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.42               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.42                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.22/1.42               (k2_tops_1 @ sk_A @ 
% 1.22/1.42                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.42                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))))),
% 1.22/1.42      inference('sup-', [status(thm)], ['43', '44'])).
% 1.22/1.42  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 1.22/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.42  thf('47', plain,
% 1.22/1.42      (((k2_pre_topc @ sk_A @ 
% 1.22/1.42         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.42          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.22/1.42         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.42            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.42             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.22/1.42            (k2_tops_1 @ sk_A @ 
% 1.22/1.42             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.42              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.22/1.42      inference('demod', [status(thm)], ['45', '46'])).
% 1.22/1.42  thf('48', plain,
% 1.22/1.42      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.22/1.42         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.22/1.42      inference('sup-', [status(thm)], ['35', '36'])).
% 1.22/1.42  thf('49', plain,
% 1.22/1.42      (![X22 : $i, X23 : $i]:
% 1.22/1.42         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 1.22/1.42           = (k3_xboole_0 @ X22 @ X23))),
% 1.22/1.42      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.22/1.42  thf('50', plain,
% 1.22/1.42      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.42         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.22/1.42         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.22/1.42      inference('sup+', [status(thm)], ['48', '49'])).
% 1.22/1.42  thf('51', plain,
% 1.22/1.42      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.22/1.42      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.22/1.42  thf('52', plain,
% 1.22/1.42      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.42         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.22/1.42         = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.22/1.42      inference('demod', [status(thm)], ['50', '51'])).
% 1.22/1.42  thf('53', plain,
% 1.22/1.42      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.22/1.42        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.22/1.42      inference('sup-', [status(thm)], ['39', '40'])).
% 1.22/1.42  thf('54', plain,
% 1.22/1.42      (![X27 : $i, X28 : $i]:
% 1.22/1.42         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 1.22/1.42          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 1.22/1.42      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.22/1.42  thf('55', plain,
% 1.22/1.42      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.42         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.22/1.42         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.42            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 1.22/1.42      inference('sup-', [status(thm)], ['53', '54'])).
% 1.22/1.42  thf('56', plain,
% 1.22/1.42      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.22/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.42  thf(involutiveness_k3_subset_1, axiom,
% 1.22/1.42    (![A:$i,B:$i]:
% 1.22/1.42     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.22/1.42       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.22/1.42  thf('57', plain,
% 1.22/1.42      (![X32 : $i, X33 : $i]:
% 1.22/1.42         (((k3_subset_1 @ X33 @ (k3_subset_1 @ X33 @ X32)) = (X32))
% 1.22/1.42          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33)))),
% 1.22/1.42      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.22/1.42  thf('58', plain,
% 1.22/1.42      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.42         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.22/1.42      inference('sup-', [status(thm)], ['56', '57'])).
% 1.22/1.42  thf('59', plain,
% 1.22/1.42      (((sk_B)
% 1.22/1.42         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.42            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 1.22/1.42      inference('demod', [status(thm)], ['55', '58'])).
% 1.22/1.42  thf('60', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.22/1.42      inference('sup+', [status(thm)], ['52', '59'])).
% 1.22/1.42  thf('61', plain,
% 1.22/1.42      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.22/1.42      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.22/1.42  thf(t100_xboole_1, axiom,
% 1.22/1.42    (![A:$i,B:$i]:
% 1.22/1.42     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.22/1.42  thf('62', plain,
% 1.22/1.42      (![X4 : $i, X5 : $i]:
% 1.22/1.42         ((k4_xboole_0 @ X4 @ X5)
% 1.22/1.42           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.22/1.42      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.22/1.42  thf('63', plain,
% 1.22/1.42      (![X0 : $i, X1 : $i]:
% 1.22/1.42         ((k4_xboole_0 @ X0 @ X1)
% 1.22/1.42           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.22/1.42      inference('sup+', [status(thm)], ['61', '62'])).
% 1.22/1.42  thf('64', plain,
% 1.22/1.42      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.22/1.42         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.22/1.42      inference('sup+', [status(thm)], ['60', '63'])).
% 1.22/1.42  thf('65', plain,
% 1.22/1.42      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.22/1.42         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.22/1.42      inference('sup-', [status(thm)], ['35', '36'])).
% 1.22/1.42  thf('66', plain,
% 1.22/1.42      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.22/1.42         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.22/1.42      inference('sup+', [status(thm)], ['64', '65'])).
% 1.22/1.42  thf('67', plain,
% 1.22/1.42      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.42         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.22/1.42      inference('sup-', [status(thm)], ['56', '57'])).
% 1.22/1.42  thf('68', plain,
% 1.22/1.42      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.22/1.42         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.22/1.42      inference('sup+', [status(thm)], ['64', '65'])).
% 1.22/1.42  thf('69', plain,
% 1.22/1.42      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.42         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.22/1.42      inference('demod', [status(thm)], ['67', '68'])).
% 1.22/1.42  thf('70', plain,
% 1.22/1.42      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.22/1.42         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.22/1.42      inference('sup+', [status(thm)], ['64', '65'])).
% 1.22/1.42  thf('71', plain,
% 1.22/1.42      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.42         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.22/1.42      inference('demod', [status(thm)], ['67', '68'])).
% 1.22/1.42  thf('72', plain,
% 1.22/1.42      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.22/1.42         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.22/1.42      inference('sup+', [status(thm)], ['64', '65'])).
% 1.22/1.42  thf('73', plain,
% 1.22/1.42      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.22/1.42         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.22/1.42      inference('demod', [status(thm)], ['67', '68'])).
% 1.22/1.42  thf('74', plain,
% 1.22/1.42      (((k2_pre_topc @ sk_A @ sk_B)
% 1.22/1.42         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.22/1.42            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.22/1.42      inference('demod', [status(thm)],
% 1.22/1.42                ['47', '66', '69', '70', '71', '72', '73'])).
% 1.22/1.42  thf('75', plain,
% 1.22/1.42      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.22/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.42  thf(redefinition_k7_subset_1, axiom,
% 1.22/1.42    (![A:$i,B:$i,C:$i]:
% 1.22/1.42     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.22/1.42       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.22/1.42  thf('76', plain,
% 1.22/1.42      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.22/1.42         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 1.22/1.42          | ((k7_subset_1 @ X38 @ X37 @ X39) = (k4_xboole_0 @ X37 @ X39)))),
% 1.22/1.42      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.22/1.42  thf('77', plain,
% 1.22/1.42      (![X0 : $i]:
% 1.22/1.42         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.22/1.42           = (k4_xboole_0 @ sk_B @ X0))),
% 1.22/1.42      inference('sup-', [status(thm)], ['75', '76'])).
% 1.22/1.42  thf('78', plain,
% 1.22/1.42      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.42          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.22/1.42             (k1_tops_1 @ sk_A @ sk_B))))
% 1.22/1.42         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.42                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.22/1.42                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.22/1.42      inference('split', [status(esa)], ['0'])).
% 1.22/1.42  thf('79', plain,
% 1.22/1.42      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.42          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.22/1.42         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.42                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.22/1.42                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.22/1.42      inference('sup+', [status(thm)], ['77', '78'])).
% 1.22/1.42  thf('80', plain,
% 1.22/1.42      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 1.22/1.42      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.22/1.42  thf(t44_xboole_1, axiom,
% 1.22/1.42    (![A:$i,B:$i,C:$i]:
% 1.22/1.42     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 1.22/1.42       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.22/1.42  thf('81', plain,
% 1.22/1.42      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.22/1.42         ((r1_tarski @ X19 @ (k2_xboole_0 @ X20 @ X21))
% 1.22/1.42          | ~ (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X21))),
% 1.22/1.42      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.22/1.42  thf('82', plain,
% 1.22/1.42      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.22/1.42      inference('sup-', [status(thm)], ['80', '81'])).
% 1.22/1.42  thf('83', plain,
% 1.22/1.42      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.22/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.42  thf('84', plain,
% 1.22/1.42      (![X43 : $i, X44 : $i]:
% 1.22/1.42         ((r1_tarski @ X43 @ X44) | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44)))),
% 1.22/1.42      inference('cnf', [status(esa)], [t3_subset])).
% 1.22/1.42  thf('85', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.22/1.42      inference('sup-', [status(thm)], ['83', '84'])).
% 1.22/1.42  thf(t1_xboole_1, axiom,
% 1.22/1.42    (![A:$i,B:$i,C:$i]:
% 1.22/1.42     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.22/1.42       ( r1_tarski @ A @ C ) ))).
% 1.22/1.42  thf('86', plain,
% 1.22/1.42      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.22/1.42         (~ (r1_tarski @ X9 @ X10)
% 1.22/1.42          | ~ (r1_tarski @ X10 @ X11)
% 1.22/1.42          | (r1_tarski @ X9 @ X11))),
% 1.22/1.42      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.22/1.42  thf('87', plain,
% 1.22/1.42      (![X0 : $i]:
% 1.22/1.42         ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 1.22/1.42      inference('sup-', [status(thm)], ['85', '86'])).
% 1.22/1.42  thf('88', plain,
% 1.22/1.42      (![X0 : $i]:
% 1.22/1.42         (r1_tarski @ sk_B @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.22/1.42      inference('sup-', [status(thm)], ['82', '87'])).
% 1.22/1.42  thf('89', plain,
% 1.22/1.42      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.22/1.42         ((r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 1.22/1.42          | ~ (r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 1.22/1.42      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.22/1.42  thf('90', plain,
% 1.22/1.42      (![X0 : $i]:
% 1.22/1.42         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 1.22/1.42      inference('sup-', [status(thm)], ['88', '89'])).
% 1.22/1.42  thf('91', plain,
% 1.22/1.42      (![X43 : $i, X45 : $i]:
% 1.22/1.42         ((m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X45)) | ~ (r1_tarski @ X43 @ X45))),
% 1.22/1.42      inference('cnf', [status(esa)], [t3_subset])).
% 1.22/1.42  thf('92', plain,
% 1.22/1.42      (![X0 : $i]:
% 1.22/1.42         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 1.22/1.42          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.22/1.42      inference('sup-', [status(thm)], ['90', '91'])).
% 1.22/1.42  thf('93', plain,
% 1.22/1.42      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.22/1.42         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.22/1.42         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.42                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.22/1.42                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.22/1.42      inference('sup+', [status(thm)], ['79', '92'])).
% 1.22/1.42  thf('94', plain,
% 1.22/1.42      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.22/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.42  thf(redefinition_k4_subset_1, axiom,
% 1.22/1.42    (![A:$i,B:$i,C:$i]:
% 1.22/1.42     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.22/1.42         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.22/1.42       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.22/1.42  thf('95', plain,
% 1.22/1.42      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.22/1.42         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 1.22/1.42          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X35))
% 1.22/1.42          | ((k4_subset_1 @ X35 @ X34 @ X36) = (k2_xboole_0 @ X34 @ X36)))),
% 1.22/1.42      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.22/1.42  thf('96', plain,
% 1.22/1.42      (![X0 : $i]:
% 1.22/1.42         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.22/1.42            = (k2_xboole_0 @ sk_B @ X0))
% 1.22/1.42          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.22/1.42      inference('sup-', [status(thm)], ['94', '95'])).
% 1.22/1.42  thf('97', plain,
% 1.22/1.42      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.22/1.42          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.22/1.42         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.42                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.22/1.42                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.22/1.42      inference('sup-', [status(thm)], ['93', '96'])).
% 1.22/1.42  thf('98', plain,
% 1.22/1.42      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.42          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.22/1.42         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.42                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.22/1.42                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.22/1.42      inference('sup+', [status(thm)], ['77', '78'])).
% 1.22/1.42  thf('99', plain,
% 1.22/1.42      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 1.22/1.42      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.22/1.42  thf('100', plain,
% 1.22/1.42      (![X6 : $i, X7 : $i]:
% 1.22/1.42         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 1.22/1.42      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.22/1.42  thf('101', plain,
% 1.22/1.42      (![X0 : $i, X1 : $i]:
% 1.22/1.42         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 1.22/1.42      inference('sup-', [status(thm)], ['99', '100'])).
% 1.22/1.42  thf('102', plain,
% 1.22/1.42      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.22/1.42      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.22/1.42  thf('103', plain,
% 1.22/1.42      (![X0 : $i, X1 : $i]:
% 1.22/1.42         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 1.22/1.42      inference('demod', [status(thm)], ['101', '102'])).
% 1.22/1.42  thf('104', plain,
% 1.22/1.42      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 1.22/1.42         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.42                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.22/1.42                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.22/1.42      inference('sup+', [status(thm)], ['98', '103'])).
% 1.22/1.42  thf('105', plain,
% 1.22/1.42      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.22/1.42          = (sk_B)))
% 1.22/1.42         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.42                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.22/1.42                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.22/1.42      inference('demod', [status(thm)], ['97', '104'])).
% 1.22/1.42  thf('106', plain,
% 1.22/1.42      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.22/1.42         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.42                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.22/1.42                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.22/1.42      inference('sup+', [status(thm)], ['74', '105'])).
% 1.22/1.42  thf('107', plain,
% 1.22/1.42      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.22/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.42  thf(t52_pre_topc, axiom,
% 1.22/1.42    (![A:$i]:
% 1.22/1.42     ( ( l1_pre_topc @ A ) =>
% 1.22/1.42       ( ![B:$i]:
% 1.22/1.42         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.22/1.42           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.22/1.42             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.22/1.42               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.22/1.42  thf('108', plain,
% 1.22/1.42      (![X49 : $i, X50 : $i]:
% 1.22/1.42         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 1.22/1.42          | ~ (v2_pre_topc @ X50)
% 1.22/1.42          | ((k2_pre_topc @ X50 @ X49) != (X49))
% 1.22/1.42          | (v4_pre_topc @ X49 @ X50)
% 1.22/1.42          | ~ (l1_pre_topc @ X50))),
% 1.22/1.42      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.22/1.42  thf('109', plain,
% 1.22/1.42      ((~ (l1_pre_topc @ sk_A)
% 1.22/1.42        | (v4_pre_topc @ sk_B @ sk_A)
% 1.22/1.42        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 1.22/1.42        | ~ (v2_pre_topc @ sk_A))),
% 1.22/1.42      inference('sup-', [status(thm)], ['107', '108'])).
% 1.22/1.42  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 1.22/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.42  thf('111', plain, ((v2_pre_topc @ sk_A)),
% 1.22/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.42  thf('112', plain,
% 1.22/1.42      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 1.22/1.42      inference('demod', [status(thm)], ['109', '110', '111'])).
% 1.22/1.42  thf('113', plain,
% 1.22/1.42      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 1.22/1.42         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.42                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.22/1.42                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.22/1.42      inference('sup-', [status(thm)], ['106', '112'])).
% 1.22/1.42  thf('114', plain,
% 1.22/1.42      (((v4_pre_topc @ sk_B @ sk_A))
% 1.22/1.42         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.42                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.22/1.42                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.22/1.42      inference('simplify', [status(thm)], ['113'])).
% 1.22/1.42  thf('115', plain,
% 1.22/1.42      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.22/1.42      inference('split', [status(esa)], ['33'])).
% 1.22/1.42  thf('116', plain,
% 1.22/1.42      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 1.22/1.42       ~
% 1.22/1.42       (((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.42          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.22/1.42             (k1_tops_1 @ sk_A @ sk_B))))),
% 1.22/1.42      inference('sup-', [status(thm)], ['114', '115'])).
% 1.22/1.42  thf('117', plain,
% 1.22/1.42      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 1.22/1.42       (((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.42          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.22/1.42             (k1_tops_1 @ sk_A @ sk_B))))),
% 1.22/1.42      inference('split', [status(esa)], ['0'])).
% 1.22/1.42  thf('118', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 1.22/1.42      inference('sat_resolution*', [status(thm)], ['34', '116', '117'])).
% 1.22/1.42  thf('119', plain,
% 1.22/1.42      (((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.42         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.22/1.42      inference('simpl_trail', [status(thm)], ['32', '118'])).
% 1.22/1.42  thf('120', plain,
% 1.22/1.42      (![X22 : $i, X23 : $i]:
% 1.22/1.42         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 1.22/1.42           = (k3_xboole_0 @ X22 @ X23))),
% 1.22/1.42      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.22/1.42  thf('121', plain,
% 1.22/1.42      (![X14 : $i, X15 : $i]:
% 1.22/1.42         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 1.22/1.42           = (k2_xboole_0 @ X14 @ X15))),
% 1.22/1.42      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.22/1.42  thf('122', plain,
% 1.22/1.42      (![X0 : $i, X1 : $i]:
% 1.22/1.42         ((k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.22/1.42           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 1.22/1.42      inference('sup+', [status(thm)], ['120', '121'])).
% 1.22/1.42  thf('123', plain,
% 1.22/1.42      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.22/1.42      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.22/1.42  thf('124', plain,
% 1.22/1.42      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.22/1.42      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.22/1.42  thf('125', plain,
% 1.22/1.42      (![X0 : $i, X1 : $i]:
% 1.22/1.42         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 1.22/1.42      inference('demod', [status(thm)], ['101', '102'])).
% 1.22/1.42  thf('126', plain,
% 1.22/1.42      (![X0 : $i, X1 : $i]:
% 1.22/1.42         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.22/1.42           = (X1))),
% 1.22/1.42      inference('demod', [status(thm)], ['122', '123', '124', '125'])).
% 1.22/1.42  thf('127', plain,
% 1.22/1.42      (((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.22/1.42         (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) = (sk_B))),
% 1.22/1.42      inference('sup+', [status(thm)], ['119', '126'])).
% 1.22/1.42  thf('128', plain,
% 1.22/1.42      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.22/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.42  thf(t74_tops_1, axiom,
% 1.22/1.42    (![A:$i]:
% 1.22/1.42     ( ( l1_pre_topc @ A ) =>
% 1.22/1.42       ( ![B:$i]:
% 1.22/1.42         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.22/1.42           ( ( k1_tops_1 @ A @ B ) =
% 1.22/1.42             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.22/1.42  thf('129', plain,
% 1.22/1.42      (![X59 : $i, X60 : $i]:
% 1.22/1.42         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 1.22/1.42          | ((k1_tops_1 @ X60 @ X59)
% 1.22/1.42              = (k7_subset_1 @ (u1_struct_0 @ X60) @ X59 @ 
% 1.22/1.42                 (k2_tops_1 @ X60 @ X59)))
% 1.22/1.42          | ~ (l1_pre_topc @ X60))),
% 1.22/1.42      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.22/1.42  thf('130', plain,
% 1.22/1.42      ((~ (l1_pre_topc @ sk_A)
% 1.22/1.42        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.22/1.42            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.22/1.42               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.22/1.42      inference('sup-', [status(thm)], ['128', '129'])).
% 1.22/1.42  thf('131', plain, ((l1_pre_topc @ sk_A)),
% 1.22/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.42  thf('132', plain,
% 1.22/1.42      (((k1_tops_1 @ sk_A @ sk_B)
% 1.22/1.42         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.22/1.42            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.22/1.42      inference('demod', [status(thm)], ['130', '131'])).
% 1.22/1.42  thf('133', plain,
% 1.22/1.42      (![X0 : $i]:
% 1.22/1.42         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.22/1.42           = (k4_xboole_0 @ sk_B @ X0))),
% 1.22/1.42      inference('sup-', [status(thm)], ['75', '76'])).
% 1.22/1.42  thf('134', plain,
% 1.22/1.42      (((k1_tops_1 @ sk_A @ sk_B)
% 1.22/1.42         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.22/1.42      inference('demod', [status(thm)], ['132', '133'])).
% 1.22/1.42  thf('135', plain,
% 1.22/1.42      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.22/1.42      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.22/1.42  thf('136', plain,
% 1.22/1.42      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.22/1.42         = (sk_B))),
% 1.22/1.42      inference('demod', [status(thm)], ['127', '134', '135'])).
% 1.22/1.42  thf('137', plain,
% 1.22/1.42      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.22/1.42      inference('sup-', [status(thm)], ['80', '81'])).
% 1.22/1.42  thf('138', plain,
% 1.22/1.42      (![X43 : $i, X45 : $i]:
% 1.22/1.42         ((m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X45)) | ~ (r1_tarski @ X43 @ X45))),
% 1.22/1.42      inference('cnf', [status(esa)], [t3_subset])).
% 1.22/1.42  thf('139', plain,
% 1.22/1.42      (![X0 : $i, X1 : $i]:
% 1.22/1.42         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.22/1.42      inference('sup-', [status(thm)], ['137', '138'])).
% 1.22/1.42  thf('140', plain,
% 1.22/1.42      (![X32 : $i, X33 : $i]:
% 1.22/1.42         (((k3_subset_1 @ X33 @ (k3_subset_1 @ X33 @ X32)) = (X32))
% 1.22/1.42          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33)))),
% 1.22/1.42      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.22/1.42  thf('141', plain,
% 1.22/1.42      (![X0 : $i, X1 : $i]:
% 1.22/1.42         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 1.22/1.42           (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0)) = (X0))),
% 1.22/1.42      inference('sup-', [status(thm)], ['139', '140'])).
% 1.22/1.42  thf('142', plain,
% 1.22/1.42      (((k3_subset_1 @ 
% 1.22/1.42         (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 1.22/1.42         (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.22/1.42         = (k2_tops_1 @ sk_A @ sk_B))),
% 1.22/1.42      inference('sup+', [status(thm)], ['136', '141'])).
% 1.22/1.42  thf('143', plain,
% 1.22/1.42      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 1.22/1.42         = (sk_B))),
% 1.22/1.42      inference('demod', [status(thm)], ['127', '134', '135'])).
% 1.22/1.42  thf('144', plain,
% 1.22/1.42      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.42          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.22/1.42         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.22/1.42      inference('demod', [status(thm)], ['20', '30', '31'])).
% 1.22/1.42  thf('145', plain,
% 1.22/1.42      (![X22 : $i, X23 : $i]:
% 1.22/1.42         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 1.22/1.42           = (k3_xboole_0 @ X22 @ X23))),
% 1.22/1.42      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.22/1.42  thf('146', plain,
% 1.22/1.42      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 1.22/1.42      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.22/1.42  thf('147', plain,
% 1.22/1.42      (![X43 : $i, X45 : $i]:
% 1.22/1.42         ((m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X45)) | ~ (r1_tarski @ X43 @ X45))),
% 1.22/1.42      inference('cnf', [status(esa)], [t3_subset])).
% 1.22/1.42  thf('148', plain,
% 1.22/1.42      (![X0 : $i, X1 : $i]:
% 1.22/1.42         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.22/1.42      inference('sup-', [status(thm)], ['146', '147'])).
% 1.22/1.42  thf('149', plain,
% 1.22/1.42      (![X0 : $i, X1 : $i]:
% 1.22/1.42         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 1.22/1.42      inference('sup+', [status(thm)], ['145', '148'])).
% 1.22/1.42  thf('150', plain,
% 1.22/1.42      (![X27 : $i, X28 : $i]:
% 1.22/1.42         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 1.22/1.42          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 1.22/1.42      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.22/1.42  thf('151', plain,
% 1.22/1.42      (![X0 : $i, X1 : $i]:
% 1.22/1.42         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.22/1.42           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.22/1.42      inference('sup-', [status(thm)], ['149', '150'])).
% 1.22/1.42  thf('152', plain,
% 1.22/1.42      ((((k3_subset_1 @ sk_B @ (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.22/1.42          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.22/1.42         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.22/1.42      inference('sup+', [status(thm)], ['144', '151'])).
% 1.22/1.42  thf('153', plain,
% 1.22/1.42      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.42          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.22/1.42         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.22/1.42      inference('demod', [status(thm)], ['20', '30', '31'])).
% 1.22/1.42  thf('154', plain,
% 1.22/1.42      (((k1_tops_1 @ sk_A @ sk_B)
% 1.22/1.42         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.22/1.42      inference('demod', [status(thm)], ['132', '133'])).
% 1.22/1.42  thf('155', plain,
% 1.22/1.42      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.22/1.42          = (k1_tops_1 @ sk_A @ sk_B)))
% 1.22/1.42         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.22/1.42      inference('demod', [status(thm)], ['152', '153', '154'])).
% 1.22/1.42  thf('156', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 1.22/1.42      inference('sat_resolution*', [status(thm)], ['34', '116', '117'])).
% 1.22/1.42  thf('157', plain,
% 1.22/1.42      (((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.22/1.42         = (k1_tops_1 @ sk_A @ sk_B))),
% 1.22/1.42      inference('simpl_trail', [status(thm)], ['155', '156'])).
% 1.22/1.42  thf('158', plain,
% 1.22/1.42      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.22/1.42         = (k2_tops_1 @ sk_A @ sk_B))),
% 1.22/1.42      inference('demod', [status(thm)], ['142', '143', '157'])).
% 1.22/1.42  thf('159', plain,
% 1.22/1.42      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.42          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.22/1.42              (k1_tops_1 @ sk_A @ sk_B))))
% 1.22/1.42         <= (~
% 1.22/1.42             (((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.42                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.22/1.42                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.22/1.42      inference('split', [status(esa)], ['33'])).
% 1.22/1.42  thf('160', plain,
% 1.22/1.42      (![X0 : $i]:
% 1.22/1.42         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.22/1.42           = (k4_xboole_0 @ sk_B @ X0))),
% 1.22/1.42      inference('sup-', [status(thm)], ['75', '76'])).
% 1.22/1.42  thf('161', plain,
% 1.22/1.42      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.22/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.42  thf(t44_tops_1, axiom,
% 1.22/1.42    (![A:$i]:
% 1.22/1.42     ( ( l1_pre_topc @ A ) =>
% 1.22/1.42       ( ![B:$i]:
% 1.22/1.42         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.22/1.42           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 1.22/1.42  thf('162', plain,
% 1.22/1.42      (![X51 : $i, X52 : $i]:
% 1.22/1.42         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 1.22/1.43          | (r1_tarski @ (k1_tops_1 @ X52 @ X51) @ X51)
% 1.22/1.43          | ~ (l1_pre_topc @ X52))),
% 1.22/1.43      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.22/1.43  thf('163', plain,
% 1.22/1.43      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.22/1.43      inference('sup-', [status(thm)], ['161', '162'])).
% 1.22/1.43  thf('164', plain, ((l1_pre_topc @ sk_A)),
% 1.22/1.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.43  thf('165', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.22/1.43      inference('demod', [status(thm)], ['163', '164'])).
% 1.22/1.43  thf('166', plain,
% 1.22/1.43      (![X43 : $i, X45 : $i]:
% 1.22/1.43         ((m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X45)) | ~ (r1_tarski @ X43 @ X45))),
% 1.22/1.43      inference('cnf', [status(esa)], [t3_subset])).
% 1.22/1.43  thf('167', plain,
% 1.22/1.43      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 1.22/1.43      inference('sup-', [status(thm)], ['165', '166'])).
% 1.22/1.43  thf('168', plain,
% 1.22/1.43      (![X27 : $i, X28 : $i]:
% 1.22/1.43         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 1.22/1.43          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 1.22/1.43      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.22/1.43  thf('169', plain,
% 1.22/1.43      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.22/1.43         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.22/1.43      inference('sup-', [status(thm)], ['167', '168'])).
% 1.22/1.43  thf('170', plain,
% 1.22/1.43      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.43          != (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.22/1.43         <= (~
% 1.22/1.43             (((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.43                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.22/1.43                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.22/1.43      inference('demod', [status(thm)], ['159', '160', '169'])).
% 1.22/1.43  thf('171', plain,
% 1.22/1.43      (~
% 1.22/1.43       (((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.43          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.22/1.43             (k1_tops_1 @ sk_A @ sk_B))))),
% 1.22/1.43      inference('sat_resolution*', [status(thm)], ['34', '116'])).
% 1.22/1.43  thf('172', plain,
% 1.22/1.43      (((k2_tops_1 @ sk_A @ sk_B)
% 1.22/1.43         != (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.22/1.43      inference('simpl_trail', [status(thm)], ['170', '171'])).
% 1.22/1.43  thf('173', plain, ($false),
% 1.22/1.43      inference('simplify_reflect-', [status(thm)], ['158', '172'])).
% 1.22/1.43  
% 1.22/1.43  % SZS output end Refutation
% 1.22/1.43  
% 1.22/1.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
