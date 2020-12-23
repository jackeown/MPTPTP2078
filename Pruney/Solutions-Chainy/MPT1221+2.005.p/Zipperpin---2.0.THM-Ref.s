%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vzd0mnjE9i

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:42 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 761 expanded)
%              Number of leaves         :   33 ( 236 expanded)
%              Depth                    :   22
%              Number of atoms          :  919 (7100 expanded)
%              Number of equality atoms :   48 ( 297 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t29_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_tops_1])).

thf('0',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('4',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('9',plain,(
    ! [X25: $i] :
      ( ( l1_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('10',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X9 @ X10 )
        = ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('13',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('15',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('16',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('18',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','19'])).

thf('21',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('22',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X11 ) @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('23',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('24',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k7_subset_1 @ X18 @ X19 @ X17 )
        = ( k9_subset_1 @ X18 @ X19 @ ( k3_subset_1 @ X18 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','19'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('32',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['4','19'])).

thf('34',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_subset_1 @ X16 @ X14 @ X15 )
        = ( k3_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
        = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['29','36'])).

thf('38',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','37'])).

thf('39',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('43',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['42','47'])).

thf('49',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['39','48'])).

thf('50',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('51',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['38','51'])).

thf('53',plain,
    ( ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['21','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('55',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('59',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v4_pre_topc @ X23 @ X24 )
      | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k2_struct_0 @ X24 ) @ X23 ) @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('60',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,
    ( ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['55','63'])).

thf('65',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('67',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('68',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['56'])).

thf('69',plain,
    ( ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('71',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('72',plain,
    ( ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('74',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k2_struct_0 @ X24 ) @ X23 ) @ X24 )
      | ( v4_pre_topc @ X23 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('75',plain,
    ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf('80',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('81',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['56'])).

thf('83',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['65','81','82'])).

thf('84',plain,(
    v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['64','83'])).

thf('85',plain,
    ( $false
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['1','20','84'])).

thf('86',plain,(
    ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['65','81'])).

thf('87',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['85','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vzd0mnjE9i
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:53:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.68  % Solved by: fo/fo7.sh
% 0.49/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.68  % done 389 iterations in 0.219s
% 0.49/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.68  % SZS output start Refutation
% 0.49/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.49/0.68  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.49/0.68  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.49/0.68  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.49/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.49/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.49/0.68  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.49/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.68  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.49/0.68  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.49/0.68  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.49/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.49/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.68  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.49/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.68  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.49/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.68  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.49/0.68  thf(t29_tops_1, conjecture,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( l1_pre_topc @ A ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.68           ( ( v4_pre_topc @ B @ A ) <=>
% 0.49/0.68             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.49/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.68    (~( ![A:$i]:
% 0.49/0.68        ( ( l1_pre_topc @ A ) =>
% 0.49/0.68          ( ![B:$i]:
% 0.49/0.68            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.68              ( ( v4_pre_topc @ B @ A ) <=>
% 0.49/0.68                ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 0.49/0.68    inference('cnf.neg', [status(esa)], [t29_tops_1])).
% 0.49/0.68  thf('0', plain,
% 0.49/0.68      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.49/0.68        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('1', plain,
% 0.49/0.68      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.49/0.68         <= (~
% 0.49/0.68             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.49/0.68      inference('split', [status(esa)], ['0'])).
% 0.49/0.68  thf('2', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(d5_subset_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.49/0.68       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.49/0.68  thf('3', plain,
% 0.49/0.68      (![X9 : $i, X10 : $i]:
% 0.49/0.68         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 0.49/0.68          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.49/0.68      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.49/0.68  thf('4', plain,
% 0.49/0.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.49/0.68         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.49/0.68      inference('sup-', [status(thm)], ['2', '3'])).
% 0.49/0.68  thf(d3_struct_0, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.49/0.68  thf('5', plain,
% 0.49/0.68      (![X22 : $i]:
% 0.49/0.68         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.49/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.68  thf('6', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('7', plain,
% 0.49/0.68      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.49/0.68        | ~ (l1_struct_0 @ sk_A))),
% 0.49/0.68      inference('sup+', [status(thm)], ['5', '6'])).
% 0.49/0.68  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(dt_l1_pre_topc, axiom,
% 0.49/0.68    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.49/0.68  thf('9', plain, (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.49/0.68      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.49/0.68  thf('10', plain, ((l1_struct_0 @ sk_A)),
% 0.49/0.68      inference('sup-', [status(thm)], ['8', '9'])).
% 0.49/0.68  thf('11', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.49/0.68      inference('demod', [status(thm)], ['7', '10'])).
% 0.49/0.68  thf('12', plain,
% 0.49/0.68      (![X9 : $i, X10 : $i]:
% 0.49/0.68         (((k3_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))
% 0.49/0.68          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.49/0.68      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.49/0.68  thf('13', plain,
% 0.49/0.68      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.49/0.68         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.49/0.68      inference('sup-', [status(thm)], ['11', '12'])).
% 0.49/0.68  thf('14', plain,
% 0.49/0.68      (![X22 : $i]:
% 0.49/0.68         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.49/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.68  thf('15', plain,
% 0.49/0.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.49/0.68         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.49/0.68      inference('sup-', [status(thm)], ['2', '3'])).
% 0.49/0.68  thf('16', plain,
% 0.49/0.68      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.49/0.68          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.49/0.68        | ~ (l1_struct_0 @ sk_A))),
% 0.49/0.68      inference('sup+', [status(thm)], ['14', '15'])).
% 0.49/0.68  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.49/0.68      inference('sup-', [status(thm)], ['8', '9'])).
% 0.49/0.68  thf('18', plain,
% 0.49/0.68      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.49/0.68         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.49/0.68      inference('demod', [status(thm)], ['16', '17'])).
% 0.49/0.68  thf('19', plain,
% 0.49/0.68      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.49/0.68         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.49/0.68      inference('sup+', [status(thm)], ['13', '18'])).
% 0.49/0.68  thf('20', plain,
% 0.49/0.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.49/0.68         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.49/0.68      inference('demod', [status(thm)], ['4', '19'])).
% 0.49/0.68  thf('21', plain,
% 0.49/0.68      (![X22 : $i]:
% 0.49/0.68         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.49/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.68  thf(dt_k2_subset_1, axiom,
% 0.49/0.68    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.49/0.68  thf('22', plain,
% 0.49/0.68      (![X11 : $i]: (m1_subset_1 @ (k2_subset_1 @ X11) @ (k1_zfmisc_1 @ X11))),
% 0.49/0.68      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.49/0.68  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.49/0.68  thf('23', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 0.49/0.68      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.49/0.68  thf('24', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 0.49/0.68      inference('demod', [status(thm)], ['22', '23'])).
% 0.49/0.68  thf('25', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(t32_subset_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.49/0.68       ( ![C:$i]:
% 0.49/0.68         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.49/0.68           ( ( k7_subset_1 @ A @ B @ C ) =
% 0.49/0.68             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.49/0.68  thf('26', plain,
% 0.49/0.68      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.49/0.68          | ((k7_subset_1 @ X18 @ X19 @ X17)
% 0.49/0.68              = (k9_subset_1 @ X18 @ X19 @ (k3_subset_1 @ X18 @ X17)))
% 0.49/0.68          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.49/0.68      inference('cnf', [status(esa)], [t32_subset_1])).
% 0.49/0.68  thf('27', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.68          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.49/0.68              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.49/0.68                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['25', '26'])).
% 0.49/0.68  thf('28', plain,
% 0.49/0.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.49/0.68         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.49/0.68      inference('demod', [status(thm)], ['4', '19'])).
% 0.49/0.68  thf('29', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.68          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.49/0.68              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.49/0.68                 (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.49/0.68      inference('demod', [status(thm)], ['27', '28'])).
% 0.49/0.68  thf('30', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(dt_k3_subset_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.49/0.68       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.49/0.68  thf('31', plain,
% 0.49/0.68      (![X12 : $i, X13 : $i]:
% 0.49/0.68         ((m1_subset_1 @ (k3_subset_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12))
% 0.49/0.68          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.49/0.68      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.49/0.68  thf('32', plain,
% 0.49/0.68      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.49/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['30', '31'])).
% 0.49/0.68  thf('33', plain,
% 0.49/0.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.49/0.68         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.49/0.68      inference('demod', [status(thm)], ['4', '19'])).
% 0.49/0.68  thf('34', plain,
% 0.49/0.68      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.49/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('demod', [status(thm)], ['32', '33'])).
% 0.49/0.68  thf(redefinition_k9_subset_1, axiom,
% 0.49/0.68    (![A:$i,B:$i,C:$i]:
% 0.49/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.49/0.68       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.49/0.68  thf('35', plain,
% 0.49/0.68      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.49/0.68         (((k9_subset_1 @ X16 @ X14 @ X15) = (k3_xboole_0 @ X14 @ X15))
% 0.49/0.68          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.49/0.68      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.49/0.68  thf('36', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.49/0.68           (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.49/0.68           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['34', '35'])).
% 0.49/0.68  thf('37', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.49/0.68          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.49/0.68              = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.49/0.68      inference('demod', [status(thm)], ['29', '36'])).
% 0.49/0.68  thf('38', plain,
% 0.49/0.68      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.49/0.68         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.49/0.68            (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['24', '37'])).
% 0.49/0.68  thf('39', plain,
% 0.49/0.68      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.49/0.68         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.49/0.68      inference('sup+', [status(thm)], ['13', '18'])).
% 0.49/0.68  thf(t36_xboole_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.49/0.68  thf('40', plain,
% 0.49/0.68      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.49/0.68      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.49/0.68  thf(t28_xboole_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.49/0.68  thf('41', plain,
% 0.49/0.68      (![X2 : $i, X3 : $i]:
% 0.49/0.68         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.49/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.49/0.68  thf('42', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 0.49/0.68           = (k4_xboole_0 @ X0 @ X1))),
% 0.49/0.68      inference('sup-', [status(thm)], ['40', '41'])).
% 0.49/0.68  thf(commutativity_k2_tarski, axiom,
% 0.49/0.68    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.49/0.68  thf('43', plain,
% 0.49/0.68      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.49/0.68      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.49/0.68  thf(t12_setfam_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.49/0.68  thf('44', plain,
% 0.49/0.68      (![X20 : $i, X21 : $i]:
% 0.49/0.68         ((k1_setfam_1 @ (k2_tarski @ X20 @ X21)) = (k3_xboole_0 @ X20 @ X21))),
% 0.49/0.68      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.49/0.68  thf('45', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.49/0.68      inference('sup+', [status(thm)], ['43', '44'])).
% 0.49/0.68  thf('46', plain,
% 0.49/0.68      (![X20 : $i, X21 : $i]:
% 0.49/0.68         ((k1_setfam_1 @ (k2_tarski @ X20 @ X21)) = (k3_xboole_0 @ X20 @ X21))),
% 0.49/0.68      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.49/0.68  thf('47', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.49/0.68      inference('sup+', [status(thm)], ['45', '46'])).
% 0.49/0.68  thf('48', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.49/0.68           = (k4_xboole_0 @ X0 @ X1))),
% 0.49/0.68      inference('demod', [status(thm)], ['42', '47'])).
% 0.49/0.68  thf('49', plain,
% 0.49/0.68      (((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.49/0.68         (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.49/0.68         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.49/0.68      inference('sup+', [status(thm)], ['39', '48'])).
% 0.49/0.68  thf('50', plain,
% 0.49/0.68      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.49/0.68         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.49/0.68      inference('sup+', [status(thm)], ['13', '18'])).
% 0.49/0.68  thf('51', plain,
% 0.49/0.68      (((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.49/0.68         (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.49/0.68         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.49/0.68      inference('demod', [status(thm)], ['49', '50'])).
% 0.49/0.68  thf('52', plain,
% 0.49/0.68      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.49/0.68         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.49/0.68      inference('sup+', [status(thm)], ['38', '51'])).
% 0.49/0.68  thf('53', plain,
% 0.49/0.68      ((((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.49/0.68          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.49/0.68        | ~ (l1_struct_0 @ sk_A))),
% 0.49/0.68      inference('sup+', [status(thm)], ['21', '52'])).
% 0.49/0.68  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 0.49/0.68      inference('sup-', [status(thm)], ['8', '9'])).
% 0.49/0.68  thf('55', plain,
% 0.49/0.68      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.49/0.68         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.49/0.68      inference('demod', [status(thm)], ['53', '54'])).
% 0.49/0.68  thf('56', plain,
% 0.49/0.68      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.49/0.68        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('57', plain,
% 0.49/0.68      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.49/0.68      inference('split', [status(esa)], ['56'])).
% 0.49/0.68  thf('58', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(d6_pre_topc, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( l1_pre_topc @ A ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.49/0.68           ( ( v4_pre_topc @ B @ A ) <=>
% 0.49/0.68             ( v3_pre_topc @
% 0.49/0.68               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ 
% 0.49/0.68               A ) ) ) ) ))).
% 0.49/0.68  thf('59', plain,
% 0.49/0.68      (![X23 : $i, X24 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.49/0.68          | ~ (v4_pre_topc @ X23 @ X24)
% 0.49/0.68          | (v3_pre_topc @ 
% 0.49/0.68             (k7_subset_1 @ (u1_struct_0 @ X24) @ (k2_struct_0 @ X24) @ X23) @ 
% 0.49/0.68             X24)
% 0.49/0.68          | ~ (l1_pre_topc @ X24))),
% 0.49/0.68      inference('cnf', [status(esa)], [d6_pre_topc])).
% 0.49/0.68  thf('60', plain,
% 0.49/0.68      ((~ (l1_pre_topc @ sk_A)
% 0.49/0.68        | (v3_pre_topc @ 
% 0.49/0.68           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.49/0.68           sk_A)
% 0.49/0.68        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['58', '59'])).
% 0.49/0.68  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('62', plain,
% 0.49/0.68      (((v3_pre_topc @ 
% 0.49/0.68         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.49/0.68         sk_A)
% 0.49/0.68        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['60', '61'])).
% 0.49/0.68  thf('63', plain,
% 0.49/0.68      (((v3_pre_topc @ 
% 0.49/0.68         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.49/0.68         sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['57', '62'])).
% 0.49/0.68  thf('64', plain,
% 0.49/0.68      (((v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.49/0.68         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.49/0.68      inference('sup+', [status(thm)], ['55', '63'])).
% 0.49/0.68  thf('65', plain,
% 0.49/0.68      (~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 0.49/0.68       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.49/0.68      inference('split', [status(esa)], ['0'])).
% 0.49/0.68  thf('66', plain,
% 0.49/0.68      (![X22 : $i]:
% 0.49/0.68         (((k2_struct_0 @ X22) = (u1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.49/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.68  thf('67', plain,
% 0.49/0.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.49/0.68         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.49/0.68      inference('sup-', [status(thm)], ['2', '3'])).
% 0.49/0.68  thf('68', plain,
% 0.49/0.68      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.49/0.68         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.49/0.68      inference('split', [status(esa)], ['56'])).
% 0.49/0.68  thf('69', plain,
% 0.49/0.68      (((v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.49/0.68         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.49/0.68      inference('sup+', [status(thm)], ['67', '68'])).
% 0.49/0.68  thf('70', plain,
% 0.49/0.68      ((((v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.49/0.68         | ~ (l1_struct_0 @ sk_A)))
% 0.49/0.68         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.49/0.68      inference('sup+', [status(thm)], ['66', '69'])).
% 0.49/0.68  thf('71', plain, ((l1_struct_0 @ sk_A)),
% 0.49/0.68      inference('sup-', [status(thm)], ['8', '9'])).
% 0.49/0.68  thf('72', plain,
% 0.49/0.68      (((v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.49/0.68         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.49/0.68      inference('demod', [status(thm)], ['70', '71'])).
% 0.49/0.68  thf('73', plain,
% 0.49/0.68      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.49/0.68         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.49/0.68      inference('demod', [status(thm)], ['53', '54'])).
% 0.49/0.68  thf('74', plain,
% 0.49/0.68      (![X23 : $i, X24 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.49/0.68          | ~ (v3_pre_topc @ 
% 0.49/0.68               (k7_subset_1 @ (u1_struct_0 @ X24) @ (k2_struct_0 @ X24) @ X23) @ 
% 0.49/0.68               X24)
% 0.49/0.68          | (v4_pre_topc @ X23 @ X24)
% 0.49/0.68          | ~ (l1_pre_topc @ X24))),
% 0.49/0.68      inference('cnf', [status(esa)], [d6_pre_topc])).
% 0.49/0.68  thf('75', plain,
% 0.49/0.68      ((~ (v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.49/0.68        | ~ (l1_pre_topc @ sk_A)
% 0.49/0.68        | (v4_pre_topc @ sk_B @ sk_A)
% 0.49/0.68        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.49/0.68      inference('sup-', [status(thm)], ['73', '74'])).
% 0.49/0.68  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('77', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('78', plain,
% 0.49/0.68      ((~ (v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.49/0.68        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.49/0.68      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.49/0.68  thf('79', plain,
% 0.49/0.68      (((v4_pre_topc @ sk_B @ sk_A))
% 0.49/0.68         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['72', '78'])).
% 0.49/0.68  thf('80', plain,
% 0.49/0.68      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.49/0.68      inference('split', [status(esa)], ['0'])).
% 0.49/0.68  thf('81', plain,
% 0.49/0.68      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.49/0.68       ~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['79', '80'])).
% 0.49/0.68  thf('82', plain,
% 0.49/0.68      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.49/0.68       ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.49/0.68      inference('split', [status(esa)], ['56'])).
% 0.49/0.68  thf('83', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.49/0.68      inference('sat_resolution*', [status(thm)], ['65', '81', '82'])).
% 0.49/0.68  thf('84', plain,
% 0.49/0.68      ((v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.49/0.68      inference('simpl_trail', [status(thm)], ['64', '83'])).
% 0.49/0.68  thf('85', plain,
% 0.49/0.68      (($false)
% 0.49/0.68         <= (~
% 0.49/0.68             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 0.49/0.68      inference('demod', [status(thm)], ['1', '20', '84'])).
% 0.49/0.68  thf('86', plain,
% 0.49/0.68      (~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.49/0.68      inference('sat_resolution*', [status(thm)], ['65', '81'])).
% 0.49/0.68  thf('87', plain, ($false),
% 0.49/0.68      inference('simpl_trail', [status(thm)], ['85', '86'])).
% 0.49/0.68  
% 0.49/0.68  % SZS output end Refutation
% 0.49/0.68  
% 0.49/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
