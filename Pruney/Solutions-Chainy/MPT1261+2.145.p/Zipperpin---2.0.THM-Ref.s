%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hY2lWPpYSp

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:00 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 355 expanded)
%              Number of leaves         :   35 ( 119 expanded)
%              Depth                    :   18
%              Number of atoms          : 1119 (3962 expanded)
%              Number of equality atoms :   88 ( 276 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( ( k1_tops_1 @ X31 @ X30 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X31 ) @ X30 @ ( k2_tops_1 @ X31 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( ( k7_subset_1 @ X20 @ X19 @ X21 )
        = ( k4_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('14',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X29 @ X28 ) @ X28 )
      | ~ ( v4_pre_topc @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('20',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('26',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['11'])).

thf('27',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('29',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('31',plain,
    ( ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('35',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('38',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('42',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('51',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','51'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('53',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('56',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['54','59'])).

thf('61',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['33','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('63',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( k2_pre_topc @ X27 @ X26 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X27 ) @ X26 @ ( k2_tops_1 @ X27 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('64',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('67',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('68',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('72',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k4_subset_1 @ X17 @ X16 @ X18 )
        = ( k2_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','65','74'])).

thf('76',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['61','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('78',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X24 @ X25 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('79',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['76','82'])).

thf('84',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['23'])).

thf('85',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['11'])).

thf('87',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['24','85','86'])).

thf('88',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['22','87'])).

thf('89',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['10','88'])).

thf('90',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['23'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('92',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['24','85'])).

thf('94',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['92','93'])).

thf('95',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['89','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hY2lWPpYSp
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:51:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.71  % Solved by: fo/fo7.sh
% 0.46/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.71  % done 421 iterations in 0.252s
% 0.46/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.71  % SZS output start Refutation
% 0.46/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.71  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.46/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.71  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.46/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.71  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.46/0.71  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.46/0.71  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.71  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.71  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.46/0.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.71  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.46/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.71  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.46/0.71  thf(t77_tops_1, conjecture,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.71       ( ![B:$i]:
% 0.46/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.71           ( ( v4_pre_topc @ B @ A ) <=>
% 0.46/0.71             ( ( k2_tops_1 @ A @ B ) =
% 0.46/0.71               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.46/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.71    (~( ![A:$i]:
% 0.46/0.71        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.71          ( ![B:$i]:
% 0.46/0.71            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.71              ( ( v4_pre_topc @ B @ A ) <=>
% 0.46/0.71                ( ( k2_tops_1 @ A @ B ) =
% 0.46/0.71                  ( k7_subset_1 @
% 0.46/0.71                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 0.46/0.71    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 0.46/0.71  thf('0', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(t74_tops_1, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( l1_pre_topc @ A ) =>
% 0.46/0.71       ( ![B:$i]:
% 0.46/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.71           ( ( k1_tops_1 @ A @ B ) =
% 0.46/0.71             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.46/0.71  thf('1', plain,
% 0.46/0.71      (![X30 : $i, X31 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.46/0.71          | ((k1_tops_1 @ X31 @ X30)
% 0.46/0.71              = (k7_subset_1 @ (u1_struct_0 @ X31) @ X30 @ 
% 0.46/0.71                 (k2_tops_1 @ X31 @ X30)))
% 0.46/0.71          | ~ (l1_pre_topc @ X31))),
% 0.46/0.71      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.46/0.71  thf('2', plain,
% 0.46/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.71        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.46/0.71            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.71               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.71  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('4', plain,
% 0.46/0.71      (((k1_tops_1 @ sk_A @ sk_B)
% 0.46/0.71         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.71            (k2_tops_1 @ sk_A @ sk_B)))),
% 0.46/0.71      inference('demod', [status(thm)], ['2', '3'])).
% 0.46/0.71  thf('5', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(redefinition_k7_subset_1, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i]:
% 0.46/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.71       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.46/0.71  thf('6', plain,
% 0.46/0.71      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.46/0.71          | ((k7_subset_1 @ X20 @ X19 @ X21) = (k4_xboole_0 @ X19 @ X21)))),
% 0.46/0.71      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.46/0.71  thf('7', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.46/0.71           = (k4_xboole_0 @ sk_B @ X0))),
% 0.46/0.71      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.71  thf('8', plain,
% 0.46/0.71      (((k1_tops_1 @ sk_A @ sk_B)
% 0.46/0.71         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.46/0.71      inference('demod', [status(thm)], ['4', '7'])).
% 0.46/0.71  thf(t48_xboole_1, axiom,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.46/0.71  thf('9', plain,
% 0.46/0.71      (![X12 : $i, X13 : $i]:
% 0.46/0.71         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.46/0.71           = (k3_xboole_0 @ X12 @ X13))),
% 0.46/0.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.71  thf('10', plain,
% 0.46/0.71      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.46/0.71         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['8', '9'])).
% 0.46/0.71  thf('11', plain,
% 0.46/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.71             (k1_tops_1 @ sk_A @ sk_B)))
% 0.46/0.71        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('12', plain,
% 0.46/0.71      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.71      inference('split', [status(esa)], ['11'])).
% 0.46/0.71  thf('13', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(t69_tops_1, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( l1_pre_topc @ A ) =>
% 0.46/0.71       ( ![B:$i]:
% 0.46/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.71           ( ( v4_pre_topc @ B @ A ) =>
% 0.46/0.71             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 0.46/0.71  thf('14', plain,
% 0.46/0.71      (![X28 : $i, X29 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.46/0.71          | (r1_tarski @ (k2_tops_1 @ X29 @ X28) @ X28)
% 0.46/0.71          | ~ (v4_pre_topc @ X28 @ X29)
% 0.46/0.71          | ~ (l1_pre_topc @ X29))),
% 0.46/0.71      inference('cnf', [status(esa)], [t69_tops_1])).
% 0.46/0.71  thf('15', plain,
% 0.46/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.71        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.46/0.71        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.46/0.71      inference('sup-', [status(thm)], ['13', '14'])).
% 0.46/0.71  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('17', plain,
% 0.46/0.71      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 0.46/0.71        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['15', '16'])).
% 0.46/0.71  thf('18', plain,
% 0.46/0.71      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.46/0.71         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['12', '17'])).
% 0.46/0.71  thf(t28_xboole_1, axiom,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.71  thf('19', plain,
% 0.46/0.71      (![X5 : $i, X6 : $i]:
% 0.46/0.71         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.46/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.71  thf('20', plain,
% 0.46/0.71      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.46/0.71          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.46/0.71         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.71  thf(commutativity_k3_xboole_0, axiom,
% 0.46/0.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.46/0.71  thf('21', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.71  thf('22', plain,
% 0.46/0.71      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.46/0.71          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.46/0.71         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.71      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.71  thf('23', plain,
% 0.46/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.71          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.71              (k1_tops_1 @ sk_A @ sk_B)))
% 0.46/0.71        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('24', plain,
% 0.46/0.71      (~
% 0.46/0.71       (((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.71             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 0.46/0.71       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.46/0.71      inference('split', [status(esa)], ['23'])).
% 0.46/0.71  thf('25', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.46/0.71           = (k4_xboole_0 @ sk_B @ X0))),
% 0.46/0.71      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.71  thf('26', plain,
% 0.46/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.71             (k1_tops_1 @ sk_A @ sk_B))))
% 0.46/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.46/0.71      inference('split', [status(esa)], ['11'])).
% 0.46/0.71  thf('27', plain,
% 0.46/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.71          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.46/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.46/0.71      inference('sup+', [status(thm)], ['25', '26'])).
% 0.46/0.71  thf(t36_xboole_1, axiom,
% 0.46/0.71    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.46/0.71  thf('28', plain,
% 0.46/0.71      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.46/0.71      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.46/0.71  thf('29', plain,
% 0.46/0.71      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 0.46/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.46/0.71      inference('sup+', [status(thm)], ['27', '28'])).
% 0.46/0.71  thf('30', plain,
% 0.46/0.71      (![X5 : $i, X6 : $i]:
% 0.46/0.71         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.46/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.71  thf('31', plain,
% 0.46/0.71      ((((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.46/0.71          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.46/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.71  thf('32', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.71  thf('33', plain,
% 0.46/0.71      ((((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.46/0.71          = (k2_tops_1 @ sk_A @ sk_B)))
% 0.46/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.46/0.71      inference('demod', [status(thm)], ['31', '32'])).
% 0.46/0.71  thf('34', plain,
% 0.46/0.71      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.46/0.71      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.46/0.71  thf(t12_xboole_1, axiom,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.46/0.71  thf('35', plain,
% 0.46/0.71      (![X2 : $i, X3 : $i]:
% 0.46/0.71         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.46/0.71      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.46/0.71  thf('36', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.46/0.71      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.71  thf('37', plain,
% 0.46/0.71      (![X12 : $i, X13 : $i]:
% 0.46/0.71         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.46/0.71           = (k3_xboole_0 @ X12 @ X13))),
% 0.46/0.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.71  thf(t41_xboole_1, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i]:
% 0.46/0.71     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.46/0.71       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.46/0.71  thf('38', plain,
% 0.46/0.71      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.71         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 0.46/0.71           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 0.46/0.71      inference('cnf', [status(esa)], [t41_xboole_1])).
% 0.46/0.71  thf('39', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.71         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.46/0.71           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 0.46/0.71      inference('sup+', [status(thm)], ['37', '38'])).
% 0.46/0.71  thf('40', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.46/0.71           = (k4_xboole_0 @ X0 @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['36', '39'])).
% 0.46/0.71  thf('41', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.46/0.71      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.71  thf(t1_boole, axiom,
% 0.46/0.71    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.71  thf('42', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.46/0.71      inference('cnf', [status(esa)], [t1_boole])).
% 0.46/0.71  thf('43', plain,
% 0.46/0.71      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['41', '42'])).
% 0.46/0.71  thf('44', plain,
% 0.46/0.71      (![X12 : $i, X13 : $i]:
% 0.46/0.71         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.46/0.71           = (k3_xboole_0 @ X12 @ X13))),
% 0.46/0.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.46/0.71  thf('45', plain,
% 0.46/0.71      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['43', '44'])).
% 0.46/0.71  thf('46', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.46/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.46/0.71  thf('47', plain,
% 0.46/0.71      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['45', '46'])).
% 0.46/0.71  thf('48', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 0.46/0.71           = (k4_xboole_0 @ X0 @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['36', '39'])).
% 0.46/0.71  thf('49', plain,
% 0.46/0.71      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['47', '48'])).
% 0.46/0.71  thf('50', plain,
% 0.46/0.71      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['41', '42'])).
% 0.46/0.71  thf('51', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.46/0.71      inference('demod', [status(thm)], ['49', '50'])).
% 0.46/0.71  thf('52', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.46/0.71      inference('demod', [status(thm)], ['40', '51'])).
% 0.46/0.71  thf(t98_xboole_1, axiom,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.46/0.71  thf('53', plain,
% 0.46/0.71      (![X14 : $i, X15 : $i]:
% 0.46/0.71         ((k2_xboole_0 @ X14 @ X15)
% 0.46/0.71           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.46/0.71      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.46/0.71  thf('54', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 0.46/0.71           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['52', '53'])).
% 0.46/0.71  thf('55', plain,
% 0.46/0.71      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['41', '42'])).
% 0.46/0.71  thf('56', plain,
% 0.46/0.71      (![X14 : $i, X15 : $i]:
% 0.46/0.71         ((k2_xboole_0 @ X14 @ X15)
% 0.46/0.71           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.46/0.71      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.46/0.71  thf('57', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['55', '56'])).
% 0.46/0.71  thf('58', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.46/0.71      inference('cnf', [status(esa)], [t1_boole])).
% 0.46/0.71  thf('59', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.71      inference('sup+', [status(thm)], ['57', '58'])).
% 0.46/0.71  thf('60', plain,
% 0.46/0.71      (![X0 : $i, X1 : $i]:
% 0.46/0.71         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 0.46/0.71      inference('demod', [status(thm)], ['54', '59'])).
% 0.46/0.71  thf('61', plain,
% 0.46/0.71      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.46/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.46/0.71      inference('sup+', [status(thm)], ['33', '60'])).
% 0.46/0.71  thf('62', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(t65_tops_1, axiom,
% 0.46/0.71    (![A:$i]:
% 0.46/0.71     ( ( l1_pre_topc @ A ) =>
% 0.46/0.71       ( ![B:$i]:
% 0.46/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.71           ( ( k2_pre_topc @ A @ B ) =
% 0.46/0.71             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.46/0.71  thf('63', plain,
% 0.46/0.71      (![X26 : $i, X27 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.46/0.71          | ((k2_pre_topc @ X27 @ X26)
% 0.46/0.71              = (k4_subset_1 @ (u1_struct_0 @ X27) @ X26 @ 
% 0.46/0.71                 (k2_tops_1 @ X27 @ X26)))
% 0.46/0.71          | ~ (l1_pre_topc @ X27))),
% 0.46/0.71      inference('cnf', [status(esa)], [t65_tops_1])).
% 0.46/0.71  thf('64', plain,
% 0.46/0.71      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.71        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.46/0.71            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.71               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['62', '63'])).
% 0.46/0.71  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('66', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(dt_k2_tops_1, axiom,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( ( l1_pre_topc @ A ) & 
% 0.46/0.71         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.71       ( m1_subset_1 @
% 0.46/0.71         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.71  thf('67', plain,
% 0.46/0.71      (![X22 : $i, X23 : $i]:
% 0.46/0.71         (~ (l1_pre_topc @ X22)
% 0.46/0.71          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.46/0.71          | (m1_subset_1 @ (k2_tops_1 @ X22 @ X23) @ 
% 0.46/0.71             (k1_zfmisc_1 @ (u1_struct_0 @ X22))))),
% 0.46/0.71      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.46/0.71  thf('68', plain,
% 0.46/0.71      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.46/0.71         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.71        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.71      inference('sup-', [status(thm)], ['66', '67'])).
% 0.46/0.71  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('70', plain,
% 0.46/0.71      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 0.46/0.71        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.71      inference('demod', [status(thm)], ['68', '69'])).
% 0.46/0.71  thf('71', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(redefinition_k4_subset_1, axiom,
% 0.46/0.71    (![A:$i,B:$i,C:$i]:
% 0.46/0.71     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.46/0.71         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.46/0.71       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.46/0.71  thf('72', plain,
% 0.46/0.71      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.71         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.46/0.71          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17))
% 0.46/0.71          | ((k4_subset_1 @ X17 @ X16 @ X18) = (k2_xboole_0 @ X16 @ X18)))),
% 0.46/0.71      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.46/0.71  thf('73', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.46/0.71            = (k2_xboole_0 @ sk_B @ X0))
% 0.46/0.71          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['71', '72'])).
% 0.46/0.71  thf('74', plain,
% 0.46/0.71      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.46/0.71         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.46/0.71      inference('sup-', [status(thm)], ['70', '73'])).
% 0.46/0.71  thf('75', plain,
% 0.46/0.71      (((k2_pre_topc @ sk_A @ sk_B)
% 0.46/0.71         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.46/0.71      inference('demod', [status(thm)], ['64', '65', '74'])).
% 0.46/0.71  thf('76', plain,
% 0.46/0.71      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.46/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.46/0.71      inference('sup+', [status(thm)], ['61', '75'])).
% 0.46/0.71  thf('77', plain,
% 0.46/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf(fc1_tops_1, axiom,
% 0.46/0.71    (![A:$i,B:$i]:
% 0.46/0.71     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.46/0.71         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.46/0.71       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 0.46/0.71  thf('78', plain,
% 0.46/0.71      (![X24 : $i, X25 : $i]:
% 0.46/0.71         (~ (l1_pre_topc @ X24)
% 0.46/0.71          | ~ (v2_pre_topc @ X24)
% 0.46/0.71          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.46/0.71          | (v4_pre_topc @ (k2_pre_topc @ X24 @ X25) @ X24))),
% 0.46/0.71      inference('cnf', [status(esa)], [fc1_tops_1])).
% 0.46/0.71  thf('79', plain,
% 0.46/0.71      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.46/0.71        | ~ (v2_pre_topc @ sk_A)
% 0.46/0.71        | ~ (l1_pre_topc @ sk_A))),
% 0.46/0.71      inference('sup-', [status(thm)], ['77', '78'])).
% 0.46/0.71  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.71  thf('82', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.46/0.71      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.46/0.71  thf('83', plain,
% 0.46/0.71      (((v4_pre_topc @ sk_B @ sk_A))
% 0.46/0.71         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.46/0.71      inference('sup+', [status(thm)], ['76', '82'])).
% 0.46/0.71  thf('84', plain,
% 0.46/0.71      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.46/0.71      inference('split', [status(esa)], ['23'])).
% 0.46/0.71  thf('85', plain,
% 0.46/0.71      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.46/0.71       ~
% 0.46/0.71       (((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.71             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.46/0.71      inference('sup-', [status(thm)], ['83', '84'])).
% 0.46/0.71  thf('86', plain,
% 0.46/0.71      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 0.46/0.71       (((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.71             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.46/0.71      inference('split', [status(esa)], ['11'])).
% 0.46/0.71  thf('87', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.46/0.71      inference('sat_resolution*', [status(thm)], ['24', '85', '86'])).
% 0.46/0.71  thf('88', plain,
% 0.46/0.71      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.46/0.71         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.46/0.71      inference('simpl_trail', [status(thm)], ['22', '87'])).
% 0.46/0.71  thf('89', plain,
% 0.46/0.71      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.46/0.71         = (k2_tops_1 @ sk_A @ sk_B))),
% 0.46/0.71      inference('demod', [status(thm)], ['10', '88'])).
% 0.46/0.71  thf('90', plain,
% 0.46/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.71          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.71              (k1_tops_1 @ sk_A @ sk_B))))
% 0.46/0.71         <= (~
% 0.46/0.71             (((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.46/0.71      inference('split', [status(esa)], ['23'])).
% 0.46/0.71  thf('91', plain,
% 0.46/0.71      (![X0 : $i]:
% 0.46/0.71         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.46/0.71           = (k4_xboole_0 @ sk_B @ X0))),
% 0.46/0.71      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.71  thf('92', plain,
% 0.46/0.71      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.71          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.46/0.71         <= (~
% 0.46/0.71             (((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.71                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.71                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.46/0.71      inference('demod', [status(thm)], ['90', '91'])).
% 0.46/0.71  thf('93', plain,
% 0.46/0.71      (~
% 0.46/0.71       (((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.71          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.46/0.71             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.46/0.71      inference('sat_resolution*', [status(thm)], ['24', '85'])).
% 0.46/0.71  thf('94', plain,
% 0.46/0.71      (((k2_tops_1 @ sk_A @ sk_B)
% 0.46/0.71         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.46/0.71      inference('simpl_trail', [status(thm)], ['92', '93'])).
% 0.46/0.71  thf('95', plain, ($false),
% 0.46/0.71      inference('simplify_reflect-', [status(thm)], ['89', '94'])).
% 0.46/0.71  
% 0.46/0.71  % SZS output end Refutation
% 0.46/0.71  
% 0.46/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
