%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r9GgsshUmF

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:36 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 318 expanded)
%              Number of leaves         :   37 ( 105 expanded)
%              Depth                    :   14
%              Number of atoms          : 1161 (3912 expanded)
%              Number of equality atoms :   84 ( 230 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

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
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k7_subset_1 @ X20 @ X19 @ X21 )
        = ( k4_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( ( k2_pre_topc @ X29 @ X28 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X29 ) @ X28 @ ( k2_tops_1 @ X29 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('13',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k4_subset_1 @ X17 @ X16 @ X18 )
        = ( k2_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('22',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['21','23'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X13 @ X12 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X14 @ X15 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X14 @ X15 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['24','33'])).

thf('35',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['20','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('37',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X24 @ X25 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('38',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['35','41'])).

thf('43',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['6','44'])).

thf('46',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['5','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('48',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X27 @ X26 ) @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['49','50'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('52',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('53',plain,
    ( ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('55',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('56',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('57',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('60',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( ( k1_tops_1 @ X33 @ X32 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X33 ) @ X32 @ ( k2_tops_1 @ X33 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('61',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('64',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('65',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('66',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('68',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['22'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('71',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X31 @ X30 ) @ X30 )
      | ~ ( v4_pre_topc @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('72',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('77',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('79',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('82',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('83',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['80','89'])).

thf('91',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['79','90'])).

thf('92',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('94',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['22'])).

thf('96',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['6','44','95'])).

thf('97',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['94','96'])).

thf('98',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['68','97'])).

thf('99',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['58','98'])).

thf('100',plain,(
    $false ),
    inference(simplify,[status(thm)],['99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r9GgsshUmF
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:58:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.36/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.57  % Solved by: fo/fo7.sh
% 0.36/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.57  % done 285 iterations in 0.113s
% 0.36/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.57  % SZS output start Refutation
% 0.36/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.57  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.36/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.57  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.36/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.57  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.36/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.57  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.36/0.57  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.36/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.57  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.36/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.36/0.57  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.36/0.57  thf(t77_tops_1, conjecture,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.57           ( ( v4_pre_topc @ B @ A ) <=>
% 0.36/0.57             ( ( k2_tops_1 @ A @ B ) =
% 0.36/0.57               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.36/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.57    (~( ![A:$i]:
% 0.36/0.57        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.57          ( ![B:$i]:
% 0.36/0.57            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.57              ( ( v4_pre_topc @ B @ A ) <=>
% 0.36/0.57                ( ( k2_tops_1 @ A @ B ) =
% 0.36/0.57                  ( k7_subset_1 @
% 0.36/0.57                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.36/0.57    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.36/0.57  thf('0', plain,
% 0.36/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57              (k1_tops_1 @ sk_A @ sk_B)))
% 0.36/0.57        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('1', plain,
% 0.36/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57              (k1_tops_1 @ sk_A @ sk_B))))
% 0.36/0.57         <= (~
% 0.36/0.57             (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('split', [status(esa)], ['0'])).
% 0.36/0.57  thf('2', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(redefinition_k7_subset_1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.57       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.36/0.57  thf('3', plain,
% 0.36/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.36/0.57          | ((k7_subset_1 @ X20 @ X19 @ X21) = (k4_xboole_0 @ X19 @ X21)))),
% 0.36/0.57      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.36/0.57  thf('4', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.57           = (k4_xboole_0 @ sk_B @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.57  thf('5', plain,
% 0.36/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.36/0.57         <= (~
% 0.36/0.57             (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('demod', [status(thm)], ['1', '4'])).
% 0.36/0.57  thf('6', plain,
% 0.36/0.57      (~
% 0.36/0.57       (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.36/0.57       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.57      inference('split', [status(esa)], ['0'])).
% 0.36/0.57  thf('7', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(t65_tops_1, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( l1_pre_topc @ A ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.57           ( ( k2_pre_topc @ A @ B ) =
% 0.36/0.57             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.36/0.57  thf('8', plain,
% 0.36/0.57      (![X28 : $i, X29 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.36/0.57          | ((k2_pre_topc @ X29 @ X28)
% 0.36/0.57              = (k4_subset_1 @ (u1_struct_0 @ X29) @ X28 @ 
% 0.36/0.57                 (k2_tops_1 @ X29 @ X28)))
% 0.36/0.57          | ~ (l1_pre_topc @ X29))),
% 0.36/0.57      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.36/0.57  thf('9', plain,
% 0.36/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.57        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.36/0.57            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.57  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('11', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(dt_k2_tops_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( ( l1_pre_topc @ A ) & 
% 0.36/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.57       ( m1_subset_1 @
% 0.36/0.57         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.57  thf('12', plain,
% 0.36/0.57      (![X22 : $i, X23 : $i]:
% 0.36/0.57         (~ (l1_pre_topc @ X22)
% 0.36/0.57          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.36/0.57          | (m1_subset_1 @ (k2_tops_1 @ X22 @ X23) @ 
% 0.36/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X22))))),
% 0.36/0.57      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.36/0.57  thf('13', plain,
% 0.36/0.57      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.36/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.57  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('15', plain,
% 0.36/0.57      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.36/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('demod', [status(thm)], ['13', '14'])).
% 0.36/0.57  thf('16', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(redefinition_k4_subset_1, axiom,
% 0.36/0.57    (![A:$i,B:$i,C:$i]:
% 0.36/0.57     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.36/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.36/0.57       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.36/0.57  thf('17', plain,
% 0.36/0.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.36/0.57          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17))
% 0.36/0.57          | ((k4_subset_1 @ X17 @ X16 @ X18) = (k2_xboole_0 @ X16 @ X18)))),
% 0.36/0.57      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.36/0.57  thf('18', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.57            = (k2_xboole_0 @ sk_B @ X0))
% 0.36/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.57  thf('19', plain,
% 0.36/0.57      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.36/0.57         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['15', '18'])).
% 0.36/0.57  thf('20', plain,
% 0.36/0.57      (((k2_pre_topc @ sk_A @ sk_B)
% 0.36/0.57         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('demod', [status(thm)], ['9', '10', '19'])).
% 0.36/0.57  thf('21', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.57           = (k4_xboole_0 @ sk_B @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.57  thf('22', plain,
% 0.36/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57             (k1_tops_1 @ sk_A @ sk_B)))
% 0.36/0.57        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('23', plain,
% 0.36/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57             (k1_tops_1 @ sk_A @ sk_B))))
% 0.36/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('split', [status(esa)], ['22'])).
% 0.36/0.57  thf('24', plain,
% 0.36/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.36/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('sup+', [status(thm)], ['21', '23'])).
% 0.36/0.57  thf(t36_xboole_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.36/0.57  thf('25', plain,
% 0.36/0.57      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.36/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.36/0.57  thf(t12_xboole_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.36/0.57  thf('26', plain,
% 0.36/0.57      (![X4 : $i, X5 : $i]:
% 0.36/0.57         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.36/0.57      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.36/0.57  thf('27', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.36/0.57  thf(commutativity_k2_tarski, axiom,
% 0.36/0.57    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.36/0.57  thf('28', plain,
% 0.36/0.57      (![X12 : $i, X13 : $i]:
% 0.36/0.57         ((k2_tarski @ X13 @ X12) = (k2_tarski @ X12 @ X13))),
% 0.36/0.57      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.36/0.57  thf(l51_zfmisc_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.36/0.57  thf('29', plain,
% 0.36/0.57      (![X14 : $i, X15 : $i]:
% 0.36/0.57         ((k3_tarski @ (k2_tarski @ X14 @ X15)) = (k2_xboole_0 @ X14 @ X15))),
% 0.36/0.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.36/0.57  thf('30', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.57      inference('sup+', [status(thm)], ['28', '29'])).
% 0.36/0.57  thf('31', plain,
% 0.36/0.57      (![X14 : $i, X15 : $i]:
% 0.36/0.57         ((k3_tarski @ (k2_tarski @ X14 @ X15)) = (k2_xboole_0 @ X14 @ X15))),
% 0.36/0.57      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.36/0.57  thf('32', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.36/0.57      inference('sup+', [status(thm)], ['30', '31'])).
% 0.36/0.57  thf('33', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 0.36/0.57      inference('demod', [status(thm)], ['27', '32'])).
% 0.36/0.57  thf('34', plain,
% 0.36/0.57      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.36/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('sup+', [status(thm)], ['24', '33'])).
% 0.36/0.57  thf('35', plain,
% 0.36/0.57      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.36/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('sup+', [status(thm)], ['20', '34'])).
% 0.36/0.57  thf('36', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(fc1_tops_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.36/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.57       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.36/0.57  thf('37', plain,
% 0.36/0.57      (![X24 : $i, X25 : $i]:
% 0.36/0.57         (~ (l1_pre_topc @ X24)
% 0.36/0.57          | ~ (v2_pre_topc @ X24)
% 0.36/0.57          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.36/0.57          | (v4_pre_topc @ (k2_pre_topc @ X24 @ X25) @ X24))),
% 0.36/0.57      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.36/0.57  thf('38', plain,
% 0.36/0.57      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.36/0.57        | ~ (v2_pre_topc @ sk_A)
% 0.36/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.36/0.57  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('41', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.36/0.57      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.36/0.57  thf('42', plain,
% 0.36/0.57      (((v4_pre_topc @ sk_B @ sk_A))
% 0.36/0.57         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.36/0.57      inference('sup+', [status(thm)], ['35', '41'])).
% 0.36/0.57  thf('43', plain,
% 0.36/0.57      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.57      inference('split', [status(esa)], ['0'])).
% 0.36/0.57  thf('44', plain,
% 0.36/0.57      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.36/0.57       ~
% 0.36/0.57       (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.36/0.57  thf('45', plain,
% 0.36/0.57      (~
% 0.36/0.57       (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.57      inference('sat_resolution*', [status(thm)], ['6', '44'])).
% 0.36/0.57  thf('46', plain,
% 0.36/0.57      (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('simpl_trail', [status(thm)], ['5', '45'])).
% 0.36/0.57  thf('47', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(t44_tops_1, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( l1_pre_topc @ A ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.57           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.36/0.57  thf('48', plain,
% 0.36/0.57      (![X26 : $i, X27 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.36/0.57          | (r1_tarski @ (k1_tops_1 @ X27 @ X26) @ X26)
% 0.36/0.57          | ~ (l1_pre_topc @ X27))),
% 0.36/0.57      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.36/0.57  thf('49', plain,
% 0.36/0.57      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.36/0.57      inference('sup-', [status(thm)], ['47', '48'])).
% 0.36/0.57  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('51', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.36/0.57      inference('demod', [status(thm)], ['49', '50'])).
% 0.36/0.57  thf(t28_xboole_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.36/0.57  thf('52', plain,
% 0.36/0.57      (![X6 : $i, X7 : $i]:
% 0.36/0.57         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.36/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.36/0.57  thf('53', plain,
% 0.36/0.57      (((k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.36/0.57         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.36/0.57      inference('sup-', [status(thm)], ['51', '52'])).
% 0.36/0.57  thf(commutativity_k3_xboole_0, axiom,
% 0.36/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.36/0.57  thf('54', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.57  thf('55', plain,
% 0.36/0.57      (((k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.36/0.57         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.36/0.57      inference('demod', [status(thm)], ['53', '54'])).
% 0.36/0.57  thf(t100_xboole_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.36/0.57  thf('56', plain,
% 0.36/0.57      (![X2 : $i, X3 : $i]:
% 0.36/0.57         ((k4_xboole_0 @ X2 @ X3)
% 0.36/0.57           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.36/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.36/0.57  thf('57', plain,
% 0.36/0.57      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.36/0.57         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('sup+', [status(thm)], ['55', '56'])).
% 0.36/0.57  thf('58', plain,
% 0.36/0.57      (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57         != (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('demod', [status(thm)], ['46', '57'])).
% 0.36/0.57  thf('59', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(t74_tops_1, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( l1_pre_topc @ A ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.57           ( ( k1_tops_1 @ A @ B ) =
% 0.36/0.57             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.36/0.57  thf('60', plain,
% 0.36/0.57      (![X32 : $i, X33 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.36/0.57          | ((k1_tops_1 @ X33 @ X32)
% 0.36/0.57              = (k7_subset_1 @ (u1_struct_0 @ X33) @ X32 @ 
% 0.36/0.57                 (k2_tops_1 @ X33 @ X32)))
% 0.36/0.57          | ~ (l1_pre_topc @ X33))),
% 0.36/0.57      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.36/0.57  thf('61', plain,
% 0.36/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.57        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.36/0.57            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.57      inference('sup-', [status(thm)], ['59', '60'])).
% 0.36/0.57  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('63', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.36/0.57           = (k4_xboole_0 @ sk_B @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.57  thf('64', plain,
% 0.36/0.57      (((k1_tops_1 @ sk_A @ sk_B)
% 0.36/0.57         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.36/0.57  thf(t48_xboole_1, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.36/0.57  thf('65', plain,
% 0.36/0.57      (![X10 : $i, X11 : $i]:
% 0.36/0.57         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.36/0.57           = (k3_xboole_0 @ X10 @ X11))),
% 0.36/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.57  thf('66', plain,
% 0.36/0.57      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.36/0.57         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('sup+', [status(thm)], ['64', '65'])).
% 0.36/0.57  thf('67', plain,
% 0.36/0.57      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.36/0.57         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('sup+', [status(thm)], ['55', '56'])).
% 0.36/0.57  thf('68', plain,
% 0.36/0.57      (((k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.36/0.57         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('demod', [status(thm)], ['66', '67'])).
% 0.36/0.57  thf('69', plain,
% 0.36/0.57      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.57      inference('split', [status(esa)], ['22'])).
% 0.36/0.57  thf('70', plain,
% 0.36/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf(t69_tops_1, axiom,
% 0.36/0.57    (![A:$i]:
% 0.36/0.57     ( ( l1_pre_topc @ A ) =>
% 0.36/0.57       ( ![B:$i]:
% 0.36/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.57           ( ( v4_pre_topc @ B @ A ) =>
% 0.36/0.57             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.36/0.57  thf('71', plain,
% 0.36/0.57      (![X30 : $i, X31 : $i]:
% 0.36/0.57         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.36/0.57          | (r1_tarski @ (k2_tops_1 @ X31 @ X30) @ X30)
% 0.36/0.57          | ~ (v4_pre_topc @ X30 @ X31)
% 0.36/0.57          | ~ (l1_pre_topc @ X31))),
% 0.36/0.57      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.36/0.57  thf('72', plain,
% 0.36/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.57        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.36/0.57        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.36/0.57      inference('sup-', [status(thm)], ['70', '71'])).
% 0.36/0.57  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('74', plain,
% 0.36/0.57      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.36/0.57        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.36/0.57      inference('demod', [status(thm)], ['72', '73'])).
% 0.36/0.57  thf('75', plain,
% 0.36/0.57      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.36/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['69', '74'])).
% 0.36/0.57  thf('76', plain,
% 0.36/0.57      (![X6 : $i, X7 : $i]:
% 0.36/0.57         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.36/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.36/0.57  thf('77', plain,
% 0.36/0.57      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.36/0.57          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.36/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['75', '76'])).
% 0.36/0.57  thf('78', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.57  thf('79', plain,
% 0.36/0.57      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.36/0.57          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.36/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.57      inference('demod', [status(thm)], ['77', '78'])).
% 0.36/0.57  thf('80', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.57  thf('81', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.57  thf('82', plain,
% 0.36/0.57      (![X10 : $i, X11 : $i]:
% 0.36/0.57         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.36/0.57           = (k3_xboole_0 @ X10 @ X11))),
% 0.36/0.57      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.36/0.57  thf('83', plain,
% 0.36/0.57      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.36/0.57      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.36/0.57  thf('84', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.36/0.57      inference('sup+', [status(thm)], ['82', '83'])).
% 0.36/0.57  thf('85', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.36/0.57      inference('sup+', [status(thm)], ['81', '84'])).
% 0.36/0.57  thf('86', plain,
% 0.36/0.57      (![X6 : $i, X7 : $i]:
% 0.36/0.57         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.36/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.36/0.57  thf('87', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.36/0.57           = (k3_xboole_0 @ X1 @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['85', '86'])).
% 0.36/0.57  thf('88', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.57  thf('89', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.36/0.57           = (k3_xboole_0 @ X1 @ X0))),
% 0.36/0.57      inference('demod', [status(thm)], ['87', '88'])).
% 0.36/0.57  thf('90', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]:
% 0.36/0.57         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.36/0.57           = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.57      inference('sup+', [status(thm)], ['80', '89'])).
% 0.36/0.57  thf('91', plain,
% 0.36/0.57      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.36/0.57          = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 0.36/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.57      inference('sup+', [status(thm)], ['79', '90'])).
% 0.36/0.57  thf('92', plain,
% 0.36/0.57      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.36/0.57          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.36/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.57      inference('demod', [status(thm)], ['77', '78'])).
% 0.36/0.57  thf('93', plain,
% 0.36/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.36/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.36/0.57  thf('94', plain,
% 0.36/0.57      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.36/0.57         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.36/0.57      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.36/0.57  thf('95', plain,
% 0.36/0.57      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.36/0.57       (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.36/0.57             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.36/0.57      inference('split', [status(esa)], ['22'])).
% 0.36/0.57  thf('96', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.36/0.57      inference('sat_resolution*', [status(thm)], ['6', '44', '95'])).
% 0.36/0.57  thf('97', plain,
% 0.36/0.57      (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('simpl_trail', [status(thm)], ['94', '96'])).
% 0.36/0.57  thf('98', plain,
% 0.36/0.57      (((k2_tops_1 @ sk_A @ sk_B)
% 0.36/0.57         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.36/0.57      inference('sup+', [status(thm)], ['68', '97'])).
% 0.36/0.57  thf('99', plain, (((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B))),
% 0.36/0.57      inference('demod', [status(thm)], ['58', '98'])).
% 0.36/0.57  thf('100', plain, ($false), inference('simplify', [status(thm)], ['99'])).
% 0.36/0.57  
% 0.36/0.57  % SZS output end Refutation
% 0.36/0.57  
% 0.36/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
