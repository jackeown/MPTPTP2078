%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xMXPPmX8MW

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:40 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  189 (1017 expanded)
%              Number of leaves         :   45 ( 341 expanded)
%              Depth                    :   27
%              Number of atoms          : 1588 (9709 expanded)
%              Number of equality atoms :  117 ( 670 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_tarski @ X25 @ ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

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

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X45: $i,X46: $i] :
      ( ( r1_tarski @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      | ~ ( r1_tarski @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('12',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('14',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('15',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_tarski @ X28 @ X27 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X43 @ X44 ) )
      = ( k3_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X43: $i,X44: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X43 @ X44 ) )
      = ( k3_xboole_0 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['14','21'])).

thf('23',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('26',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('27',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['24','25','26'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('29',plain,(
    ! [X45: $i,X47: $i] :
      ( ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X47 ) )
      | ~ ( r1_tarski @ X45 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('31',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ( ( k2_pre_topc @ X57 @ X56 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X57 ) @ X56 @ ( k2_tops_1 @ X57 @ X56 ) ) )
      | ~ ( l1_pre_topc @ X57 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( k2_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['27','32'])).

thf('34',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('35',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('37',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( l1_pre_topc @ X50 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X50 @ X51 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('38',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('42',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) )
      | ( ( k4_subset_1 @ X38 @ X37 @ X39 )
        = ( k2_xboole_0 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','35','44','45'])).

thf('47',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['47'])).

thf('49',plain,(
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

thf('50',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( v4_pre_topc @ X48 @ X49 )
      | ( ( k2_pre_topc @ X49 @ X48 )
        = X48 )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['55'])).

thf('57',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34','35','44','45'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('59',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_tarski @ X25 @ ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('61',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ( ( k7_subset_1 @ X41 @ X40 @ X42 )
        = ( k4_xboole_0 @ X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['47'])).

thf('64',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('66',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_B @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['59','68'])).

thf('70',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      | ~ ( r1_tarski @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('71',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ X0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('73',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('75',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('77',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['58','77'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('79',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('80',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['57','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('83',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( l1_pre_topc @ X52 )
      | ~ ( v2_pre_topc @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X52 @ X53 ) @ X52 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('84',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['81','87'])).

thf('89',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['55'])).

thf('90',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['47'])).

thf('92',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['56','90','91'])).

thf('93',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['54','92'])).

thf('94',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['46','93'])).

thf('95',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('96',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['94','97'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('99',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('100',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      | ~ ( r1_tarski @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['98','103'])).

thf('105',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('106',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X45: $i,X47: $i] :
      ( ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X47 ) )
      | ~ ( r1_tarski @ X45 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('109',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('110',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X31 @ X32 )
        = ( k4_xboole_0 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_tarski @ X25 @ ( k2_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('115',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      | ~ ( r1_tarski @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_subset_1 @ X1 @ X1 ) @ X0 ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X14: $i,X15: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['113','120'])).

thf('122',plain,
    ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['104','121'])).

thf('123',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('124',plain,
    ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('127',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

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
    ! [X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) )
      | ( ( k1_tops_1 @ X59 @ X58 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X59 ) @ X58 @ ( k2_tops_1 @ X59 @ X58 ) ) )
      | ~ ( l1_pre_topc @ X59 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('130',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('133',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k4_xboole_0 @ X23 @ ( k4_xboole_0 @ X23 @ X24 ) )
      = ( k3_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('135',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['127','135'])).

thf('137',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['55'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('139',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['56','90'])).

thf('141',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['139','140'])).

thf('142',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['136','141'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xMXPPmX8MW
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.06/1.32  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.06/1.32  % Solved by: fo/fo7.sh
% 1.06/1.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.32  % done 3313 iterations in 0.859s
% 1.06/1.32  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.06/1.32  % SZS output start Refutation
% 1.06/1.32  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.06/1.32  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.06/1.32  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.06/1.32  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.06/1.32  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.32  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.06/1.32  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.06/1.32  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.06/1.32  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.06/1.32  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.32  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.06/1.32  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.06/1.32  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.06/1.32  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.06/1.32  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.06/1.32  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.06/1.32  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.32  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.06/1.32  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.06/1.32  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.06/1.32  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.06/1.32  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.32  thf(t7_xboole_1, axiom,
% 1.06/1.32    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.06/1.32  thf('0', plain,
% 1.06/1.32      (![X25 : $i, X26 : $i]: (r1_tarski @ X25 @ (k2_xboole_0 @ X25 @ X26))),
% 1.06/1.32      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.06/1.32  thf(t77_tops_1, conjecture,
% 1.06/1.32    (![A:$i]:
% 1.06/1.32     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.32       ( ![B:$i]:
% 1.06/1.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.32           ( ( v4_pre_topc @ B @ A ) <=>
% 1.06/1.32             ( ( k2_tops_1 @ A @ B ) =
% 1.06/1.32               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.06/1.32  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.32    (~( ![A:$i]:
% 1.06/1.32        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.32          ( ![B:$i]:
% 1.06/1.32            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.32              ( ( v4_pre_topc @ B @ A ) <=>
% 1.06/1.32                ( ( k2_tops_1 @ A @ B ) =
% 1.06/1.32                  ( k7_subset_1 @
% 1.06/1.32                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.06/1.32    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 1.06/1.32  thf('1', plain,
% 1.06/1.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf(t3_subset, axiom,
% 1.06/1.32    (![A:$i,B:$i]:
% 1.06/1.32     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.06/1.32  thf('2', plain,
% 1.06/1.32      (![X45 : $i, X46 : $i]:
% 1.06/1.32         ((r1_tarski @ X45 @ X46) | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46)))),
% 1.06/1.32      inference('cnf', [status(esa)], [t3_subset])).
% 1.06/1.32  thf('3', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.06/1.32      inference('sup-', [status(thm)], ['1', '2'])).
% 1.06/1.32  thf(t1_xboole_1, axiom,
% 1.06/1.32    (![A:$i,B:$i,C:$i]:
% 1.06/1.32     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.06/1.32       ( r1_tarski @ A @ C ) ))).
% 1.06/1.32  thf('4', plain,
% 1.06/1.32      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.06/1.32         (~ (r1_tarski @ X6 @ X7)
% 1.06/1.32          | ~ (r1_tarski @ X7 @ X8)
% 1.06/1.32          | (r1_tarski @ X6 @ X8))),
% 1.06/1.32      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.06/1.32  thf('5', plain,
% 1.06/1.32      (![X0 : $i]:
% 1.06/1.32         ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 1.06/1.32      inference('sup-', [status(thm)], ['3', '4'])).
% 1.06/1.32  thf('6', plain,
% 1.06/1.32      (![X0 : $i]:
% 1.06/1.32         (r1_tarski @ sk_B @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))),
% 1.06/1.32      inference('sup-', [status(thm)], ['0', '5'])).
% 1.06/1.32  thf(t43_xboole_1, axiom,
% 1.06/1.32    (![A:$i,B:$i,C:$i]:
% 1.06/1.32     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.06/1.32       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.06/1.32  thf('7', plain,
% 1.06/1.32      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.06/1.32         ((r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 1.06/1.32          | ~ (r1_tarski @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 1.06/1.32      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.06/1.32  thf('8', plain,
% 1.06/1.32      (![X0 : $i]:
% 1.06/1.32         (r1_tarski @ (k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)),
% 1.06/1.32      inference('sup-', [status(thm)], ['6', '7'])).
% 1.06/1.32  thf(t38_xboole_1, axiom,
% 1.06/1.32    (![A:$i,B:$i]:
% 1.06/1.32     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 1.06/1.32       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.06/1.32  thf('9', plain,
% 1.06/1.32      (![X14 : $i, X15 : $i]:
% 1.06/1.32         (((X14) = (k1_xboole_0))
% 1.06/1.32          | ~ (r1_tarski @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 1.06/1.32      inference('cnf', [status(esa)], [t38_xboole_1])).
% 1.06/1.32  thf('10', plain,
% 1.06/1.32      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 1.06/1.32      inference('sup-', [status(thm)], ['8', '9'])).
% 1.06/1.32  thf(t48_xboole_1, axiom,
% 1.06/1.32    (![A:$i,B:$i]:
% 1.06/1.32     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.06/1.32  thf('11', plain,
% 1.06/1.32      (![X23 : $i, X24 : $i]:
% 1.06/1.32         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 1.06/1.32           = (k3_xboole_0 @ X23 @ X24))),
% 1.06/1.32      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.06/1.32  thf('12', plain,
% 1.06/1.32      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 1.06/1.32         = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.06/1.32      inference('sup+', [status(thm)], ['10', '11'])).
% 1.06/1.32  thf(t3_boole, axiom,
% 1.06/1.32    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.06/1.32  thf('13', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 1.06/1.32      inference('cnf', [status(esa)], [t3_boole])).
% 1.06/1.32  thf('14', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.06/1.32      inference('demod', [status(thm)], ['12', '13'])).
% 1.06/1.32  thf(commutativity_k2_tarski, axiom,
% 1.06/1.32    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.06/1.32  thf('15', plain,
% 1.06/1.32      (![X27 : $i, X28 : $i]:
% 1.06/1.32         ((k2_tarski @ X28 @ X27) = (k2_tarski @ X27 @ X28))),
% 1.06/1.32      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.06/1.32  thf(t12_setfam_1, axiom,
% 1.06/1.32    (![A:$i,B:$i]:
% 1.06/1.32     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.06/1.32  thf('16', plain,
% 1.06/1.32      (![X43 : $i, X44 : $i]:
% 1.06/1.32         ((k1_setfam_1 @ (k2_tarski @ X43 @ X44)) = (k3_xboole_0 @ X43 @ X44))),
% 1.06/1.32      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.06/1.32  thf('17', plain,
% 1.06/1.32      (![X0 : $i, X1 : $i]:
% 1.06/1.32         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.06/1.32      inference('sup+', [status(thm)], ['15', '16'])).
% 1.06/1.32  thf('18', plain,
% 1.06/1.32      (![X43 : $i, X44 : $i]:
% 1.06/1.32         ((k1_setfam_1 @ (k2_tarski @ X43 @ X44)) = (k3_xboole_0 @ X43 @ X44))),
% 1.06/1.32      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.06/1.32  thf('19', plain,
% 1.06/1.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.06/1.32      inference('sup+', [status(thm)], ['17', '18'])).
% 1.06/1.32  thf(t100_xboole_1, axiom,
% 1.06/1.32    (![A:$i,B:$i]:
% 1.06/1.32     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.06/1.32  thf('20', plain,
% 1.06/1.32      (![X4 : $i, X5 : $i]:
% 1.06/1.32         ((k4_xboole_0 @ X4 @ X5)
% 1.06/1.32           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.06/1.32      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.06/1.32  thf('21', plain,
% 1.06/1.32      (![X0 : $i, X1 : $i]:
% 1.06/1.32         ((k4_xboole_0 @ X0 @ X1)
% 1.06/1.32           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.06/1.32      inference('sup+', [status(thm)], ['19', '20'])).
% 1.06/1.32  thf('22', plain,
% 1.06/1.32      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.06/1.32         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.06/1.32      inference('sup+', [status(thm)], ['14', '21'])).
% 1.06/1.32  thf('23', plain,
% 1.06/1.32      (![X23 : $i, X24 : $i]:
% 1.06/1.32         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 1.06/1.32           = (k3_xboole_0 @ X23 @ X24))),
% 1.06/1.32      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.06/1.32  thf('24', plain,
% 1.06/1.32      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.32         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.06/1.32         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.06/1.32      inference('sup+', [status(thm)], ['22', '23'])).
% 1.06/1.32  thf('25', plain,
% 1.06/1.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.06/1.32      inference('sup+', [status(thm)], ['17', '18'])).
% 1.06/1.32  thf('26', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.06/1.32      inference('demod', [status(thm)], ['12', '13'])).
% 1.06/1.32  thf('27', plain,
% 1.06/1.32      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.32         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.06/1.32      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.06/1.32  thf(t36_xboole_1, axiom,
% 1.06/1.32    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.06/1.32  thf('28', plain,
% 1.06/1.32      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 1.06/1.32      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.06/1.32  thf('29', plain,
% 1.06/1.32      (![X45 : $i, X47 : $i]:
% 1.06/1.32         ((m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X47)) | ~ (r1_tarski @ X45 @ X47))),
% 1.06/1.32      inference('cnf', [status(esa)], [t3_subset])).
% 1.06/1.32  thf('30', plain,
% 1.06/1.32      (![X0 : $i, X1 : $i]:
% 1.06/1.32         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.06/1.32      inference('sup-', [status(thm)], ['28', '29'])).
% 1.06/1.32  thf(t65_tops_1, axiom,
% 1.06/1.32    (![A:$i]:
% 1.06/1.32     ( ( l1_pre_topc @ A ) =>
% 1.06/1.32       ( ![B:$i]:
% 1.06/1.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.32           ( ( k2_pre_topc @ A @ B ) =
% 1.06/1.32             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.06/1.32  thf('31', plain,
% 1.06/1.32      (![X56 : $i, X57 : $i]:
% 1.06/1.32         (~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 1.06/1.32          | ((k2_pre_topc @ X57 @ X56)
% 1.06/1.32              = (k4_subset_1 @ (u1_struct_0 @ X57) @ X56 @ 
% 1.06/1.32                 (k2_tops_1 @ X57 @ X56)))
% 1.06/1.32          | ~ (l1_pre_topc @ X57))),
% 1.06/1.32      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.06/1.32  thf('32', plain,
% 1.06/1.32      (![X0 : $i, X1 : $i]:
% 1.06/1.32         (~ (l1_pre_topc @ X0)
% 1.06/1.32          | ((k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 1.06/1.32              = (k4_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.06/1.32                 (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ 
% 1.06/1.32                 (k2_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)))))),
% 1.06/1.32      inference('sup-', [status(thm)], ['30', '31'])).
% 1.06/1.32  thf('33', plain,
% 1.06/1.32      ((((k2_pre_topc @ sk_A @ 
% 1.06/1.32          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.32           (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.06/1.32          = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.32             (k2_tops_1 @ sk_A @ 
% 1.06/1.32              (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.32               (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))))
% 1.06/1.32        | ~ (l1_pre_topc @ sk_A))),
% 1.06/1.32      inference('sup+', [status(thm)], ['27', '32'])).
% 1.06/1.32  thf('34', plain,
% 1.06/1.32      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.32         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.06/1.32      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.06/1.32  thf('35', plain,
% 1.06/1.32      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.32         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.06/1.32      inference('demod', [status(thm)], ['24', '25', '26'])).
% 1.06/1.32  thf('36', plain,
% 1.06/1.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf(dt_k2_tops_1, axiom,
% 1.06/1.32    (![A:$i,B:$i]:
% 1.06/1.32     ( ( ( l1_pre_topc @ A ) & 
% 1.06/1.32         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.06/1.32       ( m1_subset_1 @
% 1.06/1.32         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.06/1.32  thf('37', plain,
% 1.06/1.32      (![X50 : $i, X51 : $i]:
% 1.06/1.32         (~ (l1_pre_topc @ X50)
% 1.06/1.32          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 1.06/1.32          | (m1_subset_1 @ (k2_tops_1 @ X50 @ X51) @ 
% 1.06/1.32             (k1_zfmisc_1 @ (u1_struct_0 @ X50))))),
% 1.06/1.32      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.06/1.32  thf('38', plain,
% 1.06/1.32      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.06/1.32         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.06/1.32        | ~ (l1_pre_topc @ sk_A))),
% 1.06/1.32      inference('sup-', [status(thm)], ['36', '37'])).
% 1.06/1.32  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf('40', plain,
% 1.06/1.32      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.06/1.32        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.32      inference('demod', [status(thm)], ['38', '39'])).
% 1.06/1.32  thf('41', plain,
% 1.06/1.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf(redefinition_k4_subset_1, axiom,
% 1.06/1.32    (![A:$i,B:$i,C:$i]:
% 1.06/1.32     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.06/1.32         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.06/1.32       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.06/1.32  thf('42', plain,
% 1.06/1.32      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.06/1.32         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 1.06/1.32          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38))
% 1.06/1.32          | ((k4_subset_1 @ X38 @ X37 @ X39) = (k2_xboole_0 @ X37 @ X39)))),
% 1.06/1.32      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.06/1.32  thf('43', plain,
% 1.06/1.32      (![X0 : $i]:
% 1.06/1.32         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.06/1.32            = (k2_xboole_0 @ sk_B @ X0))
% 1.06/1.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.06/1.32      inference('sup-', [status(thm)], ['41', '42'])).
% 1.06/1.32  thf('44', plain,
% 1.06/1.32      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.06/1.32         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.32      inference('sup-', [status(thm)], ['40', '43'])).
% 1.06/1.32  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf('46', plain,
% 1.06/1.32      (((k2_pre_topc @ sk_A @ sk_B)
% 1.06/1.32         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.32      inference('demod', [status(thm)], ['33', '34', '35', '44', '45'])).
% 1.06/1.32  thf('47', plain,
% 1.06/1.32      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.32             (k1_tops_1 @ sk_A @ sk_B)))
% 1.06/1.32        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf('48', plain,
% 1.06/1.32      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.32      inference('split', [status(esa)], ['47'])).
% 1.06/1.32  thf('49', plain,
% 1.06/1.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf(t52_pre_topc, axiom,
% 1.06/1.32    (![A:$i]:
% 1.06/1.32     ( ( l1_pre_topc @ A ) =>
% 1.06/1.32       ( ![B:$i]:
% 1.06/1.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.32           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.06/1.32             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.06/1.32               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.06/1.32  thf('50', plain,
% 1.06/1.32      (![X48 : $i, X49 : $i]:
% 1.06/1.32         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 1.06/1.32          | ~ (v4_pre_topc @ X48 @ X49)
% 1.06/1.32          | ((k2_pre_topc @ X49 @ X48) = (X48))
% 1.06/1.32          | ~ (l1_pre_topc @ X49))),
% 1.06/1.32      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.06/1.32  thf('51', plain,
% 1.06/1.32      ((~ (l1_pre_topc @ sk_A)
% 1.06/1.32        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 1.06/1.32        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.06/1.32      inference('sup-', [status(thm)], ['49', '50'])).
% 1.06/1.32  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf('53', plain,
% 1.06/1.32      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.06/1.32      inference('demod', [status(thm)], ['51', '52'])).
% 1.06/1.32  thf('54', plain,
% 1.06/1.32      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.06/1.32         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.32      inference('sup-', [status(thm)], ['48', '53'])).
% 1.06/1.32  thf('55', plain,
% 1.06/1.32      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.32              (k1_tops_1 @ sk_A @ sk_B)))
% 1.06/1.32        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf('56', plain,
% 1.06/1.32      (~
% 1.06/1.32       (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.32             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.06/1.32       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.06/1.32      inference('split', [status(esa)], ['55'])).
% 1.06/1.32  thf('57', plain,
% 1.06/1.32      (((k2_pre_topc @ sk_A @ sk_B)
% 1.06/1.32         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.32      inference('demod', [status(thm)], ['33', '34', '35', '44', '45'])).
% 1.06/1.32  thf('58', plain,
% 1.06/1.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.06/1.32      inference('sup+', [status(thm)], ['17', '18'])).
% 1.06/1.32  thf('59', plain,
% 1.06/1.32      (![X25 : $i, X26 : $i]: (r1_tarski @ X25 @ (k2_xboole_0 @ X25 @ X26))),
% 1.06/1.32      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.06/1.32  thf('60', plain,
% 1.06/1.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf(redefinition_k7_subset_1, axiom,
% 1.06/1.32    (![A:$i,B:$i,C:$i]:
% 1.06/1.32     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.32       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.06/1.32  thf('61', plain,
% 1.06/1.32      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.06/1.32         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 1.06/1.32          | ((k7_subset_1 @ X41 @ X40 @ X42) = (k4_xboole_0 @ X40 @ X42)))),
% 1.06/1.32      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.06/1.32  thf('62', plain,
% 1.06/1.32      (![X0 : $i]:
% 1.06/1.32         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.06/1.32           = (k4_xboole_0 @ sk_B @ X0))),
% 1.06/1.32      inference('sup-', [status(thm)], ['60', '61'])).
% 1.06/1.32  thf('63', plain,
% 1.06/1.32      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.32             (k1_tops_1 @ sk_A @ sk_B))))
% 1.06/1.32         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.32                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.32      inference('split', [status(esa)], ['47'])).
% 1.06/1.32  thf('64', plain,
% 1.06/1.32      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.06/1.32         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.32                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.32      inference('sup+', [status(thm)], ['62', '63'])).
% 1.06/1.32  thf('65', plain,
% 1.06/1.32      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 1.06/1.32      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.06/1.32  thf('66', plain,
% 1.06/1.32      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.06/1.32         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.32                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.32      inference('sup+', [status(thm)], ['64', '65'])).
% 1.06/1.32  thf('67', plain,
% 1.06/1.32      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.06/1.32         (~ (r1_tarski @ X6 @ X7)
% 1.06/1.32          | ~ (r1_tarski @ X7 @ X8)
% 1.06/1.32          | (r1_tarski @ X6 @ X8))),
% 1.06/1.32      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.06/1.32  thf('68', plain,
% 1.06/1.32      ((![X0 : $i]:
% 1.06/1.32          ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 1.06/1.32           | ~ (r1_tarski @ sk_B @ X0)))
% 1.06/1.32         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.32                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.32      inference('sup-', [status(thm)], ['66', '67'])).
% 1.06/1.32  thf('69', plain,
% 1.06/1.32      ((![X0 : $i]:
% 1.06/1.32          (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_xboole_0 @ sk_B @ X0)))
% 1.06/1.32         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.32                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.32      inference('sup-', [status(thm)], ['59', '68'])).
% 1.06/1.32  thf('70', plain,
% 1.06/1.32      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.06/1.32         ((r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 1.06/1.32          | ~ (r1_tarski @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 1.06/1.32      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.06/1.32  thf('71', plain,
% 1.06/1.32      ((![X0 : $i]:
% 1.06/1.32          (r1_tarski @ (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ X0))
% 1.06/1.32         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.32                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.32      inference('sup-', [status(thm)], ['69', '70'])).
% 1.06/1.32  thf('72', plain,
% 1.06/1.32      (![X14 : $i, X15 : $i]:
% 1.06/1.32         (((X14) = (k1_xboole_0))
% 1.06/1.32          | ~ (r1_tarski @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 1.06/1.32      inference('cnf', [status(esa)], [t38_xboole_1])).
% 1.06/1.32  thf('73', plain,
% 1.06/1.32      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 1.06/1.32         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.32                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.32      inference('sup-', [status(thm)], ['71', '72'])).
% 1.06/1.32  thf('74', plain,
% 1.06/1.32      (![X23 : $i, X24 : $i]:
% 1.06/1.32         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 1.06/1.32           = (k3_xboole_0 @ X23 @ X24))),
% 1.06/1.32      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.06/1.32  thf('75', plain,
% 1.06/1.32      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 1.06/1.32          = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 1.06/1.32         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.32                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.32      inference('sup+', [status(thm)], ['73', '74'])).
% 1.06/1.32  thf('76', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 1.06/1.32      inference('cnf', [status(esa)], [t3_boole])).
% 1.06/1.32  thf('77', plain,
% 1.06/1.32      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32          = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 1.06/1.32         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.32                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.32      inference('demod', [status(thm)], ['75', '76'])).
% 1.06/1.32  thf('78', plain,
% 1.06/1.32      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.06/1.32         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.32                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.32      inference('sup+', [status(thm)], ['58', '77'])).
% 1.06/1.32  thf(t22_xboole_1, axiom,
% 1.06/1.32    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.06/1.32  thf('79', plain,
% 1.06/1.32      (![X9 : $i, X10 : $i]:
% 1.06/1.32         ((k2_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)) = (X9))),
% 1.06/1.32      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.06/1.32  thf('80', plain,
% 1.06/1.32      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 1.06/1.32         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.32                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.32      inference('sup+', [status(thm)], ['78', '79'])).
% 1.06/1.32  thf('81', plain,
% 1.06/1.32      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.06/1.32         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.32                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.32      inference('sup+', [status(thm)], ['57', '80'])).
% 1.06/1.32  thf('82', plain,
% 1.06/1.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf(fc1_tops_1, axiom,
% 1.06/1.32    (![A:$i,B:$i]:
% 1.06/1.32     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.06/1.32         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.06/1.32       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 1.06/1.32  thf('83', plain,
% 1.06/1.32      (![X52 : $i, X53 : $i]:
% 1.06/1.32         (~ (l1_pre_topc @ X52)
% 1.06/1.32          | ~ (v2_pre_topc @ X52)
% 1.06/1.32          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 1.06/1.32          | (v4_pre_topc @ (k2_pre_topc @ X52 @ X53) @ X52))),
% 1.06/1.32      inference('cnf', [status(esa)], [fc1_tops_1])).
% 1.06/1.32  thf('84', plain,
% 1.06/1.32      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 1.06/1.32        | ~ (v2_pre_topc @ sk_A)
% 1.06/1.32        | ~ (l1_pre_topc @ sk_A))),
% 1.06/1.32      inference('sup-', [status(thm)], ['82', '83'])).
% 1.06/1.32  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf('87', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 1.06/1.32      inference('demod', [status(thm)], ['84', '85', '86'])).
% 1.06/1.32  thf('88', plain,
% 1.06/1.32      (((v4_pre_topc @ sk_B @ sk_A))
% 1.06/1.32         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.32                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.32      inference('sup+', [status(thm)], ['81', '87'])).
% 1.06/1.32  thf('89', plain,
% 1.06/1.32      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.06/1.32      inference('split', [status(esa)], ['55'])).
% 1.06/1.32  thf('90', plain,
% 1.06/1.32      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 1.06/1.32       ~
% 1.06/1.32       (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.32             (k1_tops_1 @ sk_A @ sk_B))))),
% 1.06/1.32      inference('sup-', [status(thm)], ['88', '89'])).
% 1.06/1.32  thf('91', plain,
% 1.06/1.32      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 1.06/1.32       (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.32             (k1_tops_1 @ sk_A @ sk_B))))),
% 1.06/1.32      inference('split', [status(esa)], ['47'])).
% 1.06/1.32  thf('92', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 1.06/1.32      inference('sat_resolution*', [status(thm)], ['56', '90', '91'])).
% 1.06/1.32  thf('93', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 1.06/1.32      inference('simpl_trail', [status(thm)], ['54', '92'])).
% 1.06/1.32  thf('94', plain,
% 1.06/1.32      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.32      inference('demod', [status(thm)], ['46', '93'])).
% 1.06/1.32  thf('95', plain,
% 1.06/1.32      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 1.06/1.32      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.06/1.32  thf(t44_xboole_1, axiom,
% 1.06/1.32    (![A:$i,B:$i,C:$i]:
% 1.06/1.32     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 1.06/1.32       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.06/1.32  thf('96', plain,
% 1.06/1.32      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.06/1.32         ((r1_tarski @ X20 @ (k2_xboole_0 @ X21 @ X22))
% 1.06/1.32          | ~ (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X22))),
% 1.06/1.32      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.06/1.32  thf('97', plain,
% 1.06/1.32      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.06/1.32      inference('sup-', [status(thm)], ['95', '96'])).
% 1.06/1.32  thf('98', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 1.06/1.32      inference('sup+', [status(thm)], ['94', '97'])).
% 1.06/1.32  thf(t2_boole, axiom,
% 1.06/1.32    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.06/1.32  thf('99', plain,
% 1.06/1.32      (![X11 : $i]: ((k3_xboole_0 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 1.06/1.32      inference('cnf', [status(esa)], [t2_boole])).
% 1.06/1.32  thf('100', plain,
% 1.06/1.32      (![X9 : $i, X10 : $i]:
% 1.06/1.32         ((k2_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)) = (X9))),
% 1.06/1.32      inference('cnf', [status(esa)], [t22_xboole_1])).
% 1.06/1.32  thf('101', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.06/1.32      inference('sup+', [status(thm)], ['99', '100'])).
% 1.06/1.32  thf('102', plain,
% 1.06/1.32      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.06/1.32         ((r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 1.06/1.32          | ~ (r1_tarski @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 1.06/1.32      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.06/1.32  thf('103', plain,
% 1.06/1.32      (![X0 : $i, X1 : $i]:
% 1.06/1.32         (~ (r1_tarski @ X1 @ X0)
% 1.06/1.32          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 1.06/1.32      inference('sup-', [status(thm)], ['101', '102'])).
% 1.06/1.32  thf('104', plain,
% 1.06/1.32      ((r1_tarski @ (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ 
% 1.06/1.32        k1_xboole_0)),
% 1.06/1.32      inference('sup-', [status(thm)], ['98', '103'])).
% 1.06/1.32  thf('105', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 1.06/1.32      inference('cnf', [status(esa)], [t3_boole])).
% 1.06/1.32  thf('106', plain,
% 1.06/1.32      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 1.06/1.32      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.06/1.32  thf('107', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.06/1.32      inference('sup+', [status(thm)], ['105', '106'])).
% 1.06/1.32  thf('108', plain,
% 1.06/1.32      (![X45 : $i, X47 : $i]:
% 1.06/1.32         ((m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X47)) | ~ (r1_tarski @ X45 @ X47))),
% 1.06/1.32      inference('cnf', [status(esa)], [t3_subset])).
% 1.06/1.32  thf('109', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.06/1.32      inference('sup-', [status(thm)], ['107', '108'])).
% 1.06/1.32  thf(d5_subset_1, axiom,
% 1.06/1.32    (![A:$i,B:$i]:
% 1.06/1.32     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.32       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.06/1.32  thf('110', plain,
% 1.06/1.32      (![X31 : $i, X32 : $i]:
% 1.06/1.32         (((k3_subset_1 @ X31 @ X32) = (k4_xboole_0 @ X31 @ X32))
% 1.06/1.32          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 1.06/1.32      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.06/1.32  thf('111', plain,
% 1.06/1.32      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.06/1.32      inference('sup-', [status(thm)], ['109', '110'])).
% 1.06/1.32  thf('112', plain,
% 1.06/1.32      (![X14 : $i, X15 : $i]:
% 1.06/1.32         (((X14) = (k1_xboole_0))
% 1.06/1.32          | ~ (r1_tarski @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 1.06/1.32      inference('cnf', [status(esa)], [t38_xboole_1])).
% 1.06/1.32  thf('113', plain,
% 1.06/1.32      (![X0 : $i]:
% 1.06/1.32         (~ (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ X0)) | ((X0) = (k1_xboole_0)))),
% 1.06/1.32      inference('sup-', [status(thm)], ['111', '112'])).
% 1.06/1.32  thf('114', plain,
% 1.06/1.32      (![X25 : $i, X26 : $i]: (r1_tarski @ X25 @ (k2_xboole_0 @ X25 @ X26))),
% 1.06/1.32      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.06/1.32  thf('115', plain,
% 1.06/1.32      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.06/1.32         ((r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 1.06/1.32          | ~ (r1_tarski @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 1.06/1.32      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.06/1.32  thf('116', plain,
% 1.06/1.32      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 1.06/1.32      inference('sup-', [status(thm)], ['114', '115'])).
% 1.06/1.32  thf('117', plain,
% 1.06/1.32      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.06/1.32      inference('sup-', [status(thm)], ['109', '110'])).
% 1.06/1.32  thf('118', plain,
% 1.06/1.32      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_subset_1 @ X1 @ X1) @ X0)),
% 1.06/1.32      inference('demod', [status(thm)], ['116', '117'])).
% 1.06/1.32  thf('119', plain,
% 1.06/1.32      (![X14 : $i, X15 : $i]:
% 1.06/1.32         (((X14) = (k1_xboole_0))
% 1.06/1.32          | ~ (r1_tarski @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 1.06/1.32      inference('cnf', [status(esa)], [t38_xboole_1])).
% 1.06/1.32  thf('120', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.06/1.32      inference('sup-', [status(thm)], ['118', '119'])).
% 1.06/1.32  thf('121', plain,
% 1.06/1.32      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.06/1.32      inference('demod', [status(thm)], ['113', '120'])).
% 1.06/1.32  thf('122', plain,
% 1.06/1.32      (((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0))),
% 1.06/1.32      inference('sup-', [status(thm)], ['104', '121'])).
% 1.06/1.32  thf('123', plain,
% 1.06/1.32      (![X23 : $i, X24 : $i]:
% 1.06/1.32         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 1.06/1.32           = (k3_xboole_0 @ X23 @ X24))),
% 1.06/1.32      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.06/1.32  thf('124', plain,
% 1.06/1.32      (((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 1.06/1.32         = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.06/1.32      inference('sup+', [status(thm)], ['122', '123'])).
% 1.06/1.32  thf('125', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 1.06/1.32      inference('cnf', [status(esa)], [t3_boole])).
% 1.06/1.32  thf('126', plain,
% 1.06/1.32      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.06/1.32      inference('sup+', [status(thm)], ['17', '18'])).
% 1.06/1.32  thf('127', plain,
% 1.06/1.32      (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.32      inference('demod', [status(thm)], ['124', '125', '126'])).
% 1.06/1.32  thf('128', plain,
% 1.06/1.32      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf(t74_tops_1, axiom,
% 1.06/1.32    (![A:$i]:
% 1.06/1.32     ( ( l1_pre_topc @ A ) =>
% 1.06/1.32       ( ![B:$i]:
% 1.06/1.32         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.32           ( ( k1_tops_1 @ A @ B ) =
% 1.06/1.32             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.06/1.32  thf('129', plain,
% 1.06/1.32      (![X58 : $i, X59 : $i]:
% 1.06/1.32         (~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X59)))
% 1.06/1.32          | ((k1_tops_1 @ X59 @ X58)
% 1.06/1.32              = (k7_subset_1 @ (u1_struct_0 @ X59) @ X58 @ 
% 1.06/1.32                 (k2_tops_1 @ X59 @ X58)))
% 1.06/1.32          | ~ (l1_pre_topc @ X59))),
% 1.06/1.32      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.06/1.32  thf('130', plain,
% 1.06/1.32      ((~ (l1_pre_topc @ sk_A)
% 1.06/1.32        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.06/1.32            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.32               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.06/1.32      inference('sup-', [status(thm)], ['128', '129'])).
% 1.06/1.32  thf('131', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.32  thf('132', plain,
% 1.06/1.32      (![X0 : $i]:
% 1.06/1.32         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.06/1.32           = (k4_xboole_0 @ sk_B @ X0))),
% 1.06/1.32      inference('sup-', [status(thm)], ['60', '61'])).
% 1.06/1.32  thf('133', plain,
% 1.06/1.32      (((k1_tops_1 @ sk_A @ sk_B)
% 1.06/1.32         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.32      inference('demod', [status(thm)], ['130', '131', '132'])).
% 1.06/1.32  thf('134', plain,
% 1.06/1.32      (![X23 : $i, X24 : $i]:
% 1.06/1.32         ((k4_xboole_0 @ X23 @ (k4_xboole_0 @ X23 @ X24))
% 1.06/1.32           = (k3_xboole_0 @ X23 @ X24))),
% 1.06/1.32      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.06/1.32  thf('135', plain,
% 1.06/1.32      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.06/1.32         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.32      inference('sup+', [status(thm)], ['133', '134'])).
% 1.06/1.32  thf('136', plain,
% 1.06/1.32      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.06/1.32         = (k2_tops_1 @ sk_A @ sk_B))),
% 1.06/1.32      inference('sup+', [status(thm)], ['127', '135'])).
% 1.06/1.32  thf('137', plain,
% 1.06/1.32      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.32              (k1_tops_1 @ sk_A @ sk_B))))
% 1.06/1.32         <= (~
% 1.06/1.32             (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.32                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.32      inference('split', [status(esa)], ['55'])).
% 1.06/1.32  thf('138', plain,
% 1.06/1.32      (![X0 : $i]:
% 1.06/1.32         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.06/1.32           = (k4_xboole_0 @ sk_B @ X0))),
% 1.06/1.32      inference('sup-', [status(thm)], ['60', '61'])).
% 1.06/1.32  thf('139', plain,
% 1.06/1.32      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.06/1.32         <= (~
% 1.06/1.32             (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.32                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.06/1.32      inference('demod', [status(thm)], ['137', '138'])).
% 1.06/1.32  thf('140', plain,
% 1.06/1.32      (~
% 1.06/1.32       (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.32             (k1_tops_1 @ sk_A @ sk_B))))),
% 1.06/1.32      inference('sat_resolution*', [status(thm)], ['56', '90'])).
% 1.06/1.32  thf('141', plain,
% 1.06/1.32      (((k2_tops_1 @ sk_A @ sk_B)
% 1.06/1.32         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.32      inference('simpl_trail', [status(thm)], ['139', '140'])).
% 1.06/1.32  thf('142', plain, ($false),
% 1.06/1.32      inference('simplify_reflect-', [status(thm)], ['136', '141'])).
% 1.06/1.32  
% 1.06/1.32  % SZS output end Refutation
% 1.06/1.32  
% 1.06/1.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
