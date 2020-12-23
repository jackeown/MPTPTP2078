%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eJ5o1O13A2

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:25 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  231 (1400 expanded)
%              Number of leaves         :   46 ( 464 expanded)
%              Depth                    :   20
%              Number of atoms          : 1937 (12188 expanded)
%              Number of equality atoms :  146 ( 999 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(t76_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_tarski @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('2',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    = sk_B ),
    inference('sup-',[status(thm)],['2','5'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X23 @ X22 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('10',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['6','11'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X23 @ X22 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('18',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    = sk_B ),
    inference('sup-',[status(thm)],['2','5'])).

thf('19',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('21',plain,(
    ! [X44: $i,X46: $i] :
      ( ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X46 ) )
      | ~ ( r1_tarski @ X44 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('23',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( ( k2_tops_1 @ X52 @ X51 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X52 ) @ ( k2_pre_topc @ X52 @ X51 ) @ ( k1_tops_1 @ X52 @ X51 ) ) )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('27',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('29',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( l1_pre_topc @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X47 @ X48 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('30',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ( ( k7_subset_1 @ X40 @ X39 @ X41 )
        = ( k4_xboole_0 @ X39 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26','27','34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('38',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ( ( k1_tops_1 @ X61 @ X60 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X61 ) @ X60 @ ( k2_tops_1 @ X61 @ X60 ) ) )
      | ~ ( l1_pre_topc @ X61 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) )
      | ( ( k7_subset_1 @ X40 @ X39 @ X41 )
        = ( k4_xboole_0 @ X39 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','43'])).

thf('45',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','43'])).

thf('50',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X44: $i,X46: $i] :
      ( ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X46 ) )
      | ~ ( r1_tarski @ X44 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('56',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('58',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('59',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('62',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('63',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('64',plain,(
    ! [X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X8 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('68',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('70',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X29 @ X28 @ X30 ) @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('75',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) )
      | ( ( k4_subset_1 @ X37 @ X36 @ X38 )
        = ( k2_xboole_0 @ X36 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','77'])).

thf(t56_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('79',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ~ ( v3_pre_topc @ X53 @ X54 )
      | ~ ( r1_tarski @ X53 @ X55 )
      | ( r1_tarski @ X53 @ ( k1_tops_1 @ X54 @ X55 ) )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('84',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('85',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X29 @ X28 @ X30 ) @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ X0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_subset_1 @ X0 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_tarski @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('89',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_subset_1 @ X0 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_subset_1 @ X0 @ X0 @ k1_xboole_0 ) )
      | ( X0
        = ( k4_subset_1 @ X0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('93',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('94',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) )
      | ( ( k4_subset_1 @ X37 @ X36 @ X38 )
        = ( k2_xboole_0 @ X36 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ X0 @ X1 )
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','65'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('98',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X23 @ X22 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('101',plain,(
    ! [X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X8 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X8 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('106',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['99','110'])).

thf('112',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X23 @ X22 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('117',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['116','119'])).

thf('121',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_tarski @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['115','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('125',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['91','96','123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['91','96','123','124'])).

thf('127',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['91','96','123','124'])).

thf('128',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['128'])).

thf('130',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('133',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['128'])).

thf('134',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('135',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('136',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('140',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('141',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('142',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('143',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) ) )
      = ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X19 @ X20 ) ) @ X21 ) ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('144',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k1_setfam_1 @ ( k2_tarski @ X4 @ X5 ) ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('145',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X2 @ X1 ) ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['139','145'])).

thf('147',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X23 @ X22 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('148',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('149',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X42 @ X43 ) )
      = ( k3_xboole_0 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('150',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['147','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','65'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('154',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['146','151','154','155'])).

thf('157',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['134','156'])).

thf('158',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','43'])).

thf('159',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['157','158'])).

thf('160',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('161',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( l1_pre_topc @ X49 )
      | ~ ( v2_pre_topc @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X49 @ X50 ) @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('162',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['162','163','164'])).

thf('166',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['159','165'])).

thf('167',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['130'])).

thf('168',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['128'])).

thf('170',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['131','168','169'])).

thf('171',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['129','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['82','125','126','127','171'])).

thf('173',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','172'])).

thf('174',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('175',plain,(
    r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,
    ( sk_B
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['50','175'])).

thf('177',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['36','176'])).

thf('178',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['130'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('180',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['131','168'])).

thf('182',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['180','181'])).

thf('183',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['177','182'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eJ5o1O13A2
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:06:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.50/1.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.50/1.69  % Solved by: fo/fo7.sh
% 1.50/1.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.50/1.69  % done 3288 iterations in 1.248s
% 1.50/1.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.50/1.69  % SZS output start Refutation
% 1.50/1.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.50/1.69  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.50/1.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.50/1.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.50/1.69  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.50/1.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.50/1.69  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.50/1.69  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.50/1.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.50/1.69  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.50/1.69  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.50/1.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.50/1.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.50/1.69  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.50/1.69  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.50/1.69  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.50/1.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.50/1.69  thf(sk_B_type, type, sk_B: $i).
% 1.50/1.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.50/1.69  thf(sk_A_type, type, sk_A: $i).
% 1.50/1.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.50/1.69  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.50/1.69  thf(t76_tops_1, conjecture,
% 1.50/1.69    (![A:$i]:
% 1.50/1.69     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.50/1.69       ( ![B:$i]:
% 1.50/1.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.50/1.69           ( ( v3_pre_topc @ B @ A ) <=>
% 1.50/1.69             ( ( k2_tops_1 @ A @ B ) =
% 1.50/1.69               ( k7_subset_1 @
% 1.50/1.69                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 1.50/1.69  thf(zf_stmt_0, negated_conjecture,
% 1.50/1.69    (~( ![A:$i]:
% 1.50/1.69        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.50/1.69          ( ![B:$i]:
% 1.50/1.69            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.50/1.69              ( ( v3_pre_topc @ B @ A ) <=>
% 1.50/1.69                ( ( k2_tops_1 @ A @ B ) =
% 1.50/1.69                  ( k7_subset_1 @
% 1.50/1.69                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 1.50/1.69    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 1.50/1.69  thf('0', plain,
% 1.50/1.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.69  thf(t3_subset, axiom,
% 1.50/1.69    (![A:$i,B:$i]:
% 1.50/1.69     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.50/1.69  thf('1', plain,
% 1.50/1.69      (![X44 : $i, X45 : $i]:
% 1.50/1.69         ((r1_tarski @ X44 @ X45) | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45)))),
% 1.50/1.69      inference('cnf', [status(esa)], [t3_subset])).
% 1.50/1.69  thf('2', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.50/1.69      inference('sup-', [status(thm)], ['0', '1'])).
% 1.50/1.69  thf(t28_xboole_1, axiom,
% 1.50/1.69    (![A:$i,B:$i]:
% 1.50/1.69     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.50/1.69  thf('3', plain,
% 1.50/1.69      (![X6 : $i, X7 : $i]:
% 1.50/1.69         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 1.50/1.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.50/1.69  thf(t12_setfam_1, axiom,
% 1.50/1.69    (![A:$i,B:$i]:
% 1.50/1.69     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.50/1.69  thf('4', plain,
% 1.50/1.69      (![X42 : $i, X43 : $i]:
% 1.50/1.69         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 1.50/1.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.50/1.69  thf('5', plain,
% 1.50/1.69      (![X6 : $i, X7 : $i]:
% 1.50/1.69         (((k1_setfam_1 @ (k2_tarski @ X6 @ X7)) = (X6))
% 1.50/1.69          | ~ (r1_tarski @ X6 @ X7))),
% 1.50/1.69      inference('demod', [status(thm)], ['3', '4'])).
% 1.50/1.69  thf('6', plain,
% 1.50/1.69      (((k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))) = (sk_B))),
% 1.50/1.69      inference('sup-', [status(thm)], ['2', '5'])).
% 1.50/1.69  thf(commutativity_k2_tarski, axiom,
% 1.50/1.69    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.50/1.69  thf('7', plain,
% 1.50/1.69      (![X22 : $i, X23 : $i]:
% 1.50/1.69         ((k2_tarski @ X23 @ X22) = (k2_tarski @ X22 @ X23))),
% 1.50/1.69      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.50/1.69  thf(t100_xboole_1, axiom,
% 1.50/1.69    (![A:$i,B:$i]:
% 1.50/1.69     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.50/1.69  thf('8', plain,
% 1.50/1.69      (![X4 : $i, X5 : $i]:
% 1.50/1.69         ((k4_xboole_0 @ X4 @ X5)
% 1.50/1.69           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.50/1.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.50/1.69  thf('9', plain,
% 1.50/1.69      (![X42 : $i, X43 : $i]:
% 1.50/1.69         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 1.50/1.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.50/1.69  thf('10', plain,
% 1.50/1.69      (![X4 : $i, X5 : $i]:
% 1.50/1.69         ((k4_xboole_0 @ X4 @ X5)
% 1.50/1.69           = (k5_xboole_0 @ X4 @ (k1_setfam_1 @ (k2_tarski @ X4 @ X5))))),
% 1.50/1.69      inference('demod', [status(thm)], ['8', '9'])).
% 1.50/1.69  thf('11', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         ((k4_xboole_0 @ X0 @ X1)
% 1.50/1.69           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 1.50/1.69      inference('sup+', [status(thm)], ['7', '10'])).
% 1.50/1.69  thf('12', plain,
% 1.50/1.69      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.50/1.69         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.50/1.69      inference('sup+', [status(thm)], ['6', '11'])).
% 1.50/1.69  thf(t48_xboole_1, axiom,
% 1.50/1.69    (![A:$i,B:$i]:
% 1.50/1.69     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.50/1.69  thf('13', plain,
% 1.50/1.69      (![X17 : $i, X18 : $i]:
% 1.50/1.69         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.50/1.69           = (k3_xboole_0 @ X17 @ X18))),
% 1.50/1.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.50/1.69  thf('14', plain,
% 1.50/1.69      (![X42 : $i, X43 : $i]:
% 1.50/1.69         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 1.50/1.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.50/1.69  thf('15', plain,
% 1.50/1.69      (![X17 : $i, X18 : $i]:
% 1.50/1.69         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.50/1.69           = (k1_setfam_1 @ (k2_tarski @ X17 @ X18)))),
% 1.50/1.69      inference('demod', [status(thm)], ['13', '14'])).
% 1.50/1.69  thf('16', plain,
% 1.50/1.69      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.50/1.69         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.50/1.69         = (k1_setfam_1 @ (k2_tarski @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 1.50/1.69      inference('sup+', [status(thm)], ['12', '15'])).
% 1.50/1.69  thf('17', plain,
% 1.50/1.69      (![X22 : $i, X23 : $i]:
% 1.50/1.69         ((k2_tarski @ X23 @ X22) = (k2_tarski @ X22 @ X23))),
% 1.50/1.69      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.50/1.69  thf('18', plain,
% 1.50/1.69      (((k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))) = (sk_B))),
% 1.50/1.69      inference('sup-', [status(thm)], ['2', '5'])).
% 1.50/1.69  thf('19', plain,
% 1.50/1.69      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.50/1.69         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.50/1.69      inference('demod', [status(thm)], ['16', '17', '18'])).
% 1.50/1.69  thf(t36_xboole_1, axiom,
% 1.50/1.69    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.50/1.69  thf('20', plain,
% 1.50/1.69      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 1.50/1.69      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.50/1.69  thf('21', plain,
% 1.50/1.69      (![X44 : $i, X46 : $i]:
% 1.50/1.69         ((m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X46)) | ~ (r1_tarski @ X44 @ X46))),
% 1.50/1.69      inference('cnf', [status(esa)], [t3_subset])).
% 1.50/1.69  thf('22', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.50/1.69      inference('sup-', [status(thm)], ['20', '21'])).
% 1.50/1.69  thf(l78_tops_1, axiom,
% 1.50/1.69    (![A:$i]:
% 1.50/1.69     ( ( l1_pre_topc @ A ) =>
% 1.50/1.69       ( ![B:$i]:
% 1.50/1.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.50/1.69           ( ( k2_tops_1 @ A @ B ) =
% 1.50/1.69             ( k7_subset_1 @
% 1.50/1.69               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.50/1.69               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.50/1.69  thf('23', plain,
% 1.50/1.69      (![X51 : $i, X52 : $i]:
% 1.50/1.69         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 1.50/1.69          | ((k2_tops_1 @ X52 @ X51)
% 1.50/1.69              = (k7_subset_1 @ (u1_struct_0 @ X52) @ 
% 1.50/1.69                 (k2_pre_topc @ X52 @ X51) @ (k1_tops_1 @ X52 @ X51)))
% 1.50/1.69          | ~ (l1_pre_topc @ X52))),
% 1.50/1.69      inference('cnf', [status(esa)], [l78_tops_1])).
% 1.50/1.69  thf('24', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         (~ (l1_pre_topc @ X0)
% 1.50/1.69          | ((k2_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 1.50/1.69              = (k7_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.50/1.69                 (k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 1.50/1.69                 (k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)))))),
% 1.50/1.69      inference('sup-', [status(thm)], ['22', '23'])).
% 1.50/1.69  thf('25', plain,
% 1.50/1.69      ((((k2_tops_1 @ sk_A @ 
% 1.50/1.69          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.50/1.69           (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.50/1.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.50/1.69             (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.50/1.69             (k1_tops_1 @ sk_A @ 
% 1.50/1.69              (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.50/1.69               (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))))
% 1.50/1.69        | ~ (l1_pre_topc @ sk_A))),
% 1.50/1.69      inference('sup+', [status(thm)], ['19', '24'])).
% 1.50/1.69  thf('26', plain,
% 1.50/1.69      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.50/1.69         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.50/1.69      inference('demod', [status(thm)], ['16', '17', '18'])).
% 1.50/1.69  thf('27', plain,
% 1.50/1.69      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.50/1.69         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.50/1.69      inference('demod', [status(thm)], ['16', '17', '18'])).
% 1.50/1.69  thf('28', plain,
% 1.50/1.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.69  thf(dt_k2_pre_topc, axiom,
% 1.50/1.69    (![A:$i,B:$i]:
% 1.50/1.69     ( ( ( l1_pre_topc @ A ) & 
% 1.50/1.69         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.50/1.69       ( m1_subset_1 @
% 1.50/1.69         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.50/1.69  thf('29', plain,
% 1.50/1.69      (![X47 : $i, X48 : $i]:
% 1.50/1.69         (~ (l1_pre_topc @ X47)
% 1.50/1.69          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 1.50/1.69          | (m1_subset_1 @ (k2_pre_topc @ X47 @ X48) @ 
% 1.50/1.69             (k1_zfmisc_1 @ (u1_struct_0 @ X47))))),
% 1.50/1.69      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.50/1.69  thf('30', plain,
% 1.50/1.69      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.50/1.69         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.50/1.69        | ~ (l1_pre_topc @ sk_A))),
% 1.50/1.69      inference('sup-', [status(thm)], ['28', '29'])).
% 1.50/1.69  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 1.50/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.69  thf('32', plain,
% 1.50/1.69      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.50/1.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.69      inference('demod', [status(thm)], ['30', '31'])).
% 1.50/1.69  thf(redefinition_k7_subset_1, axiom,
% 1.50/1.69    (![A:$i,B:$i,C:$i]:
% 1.50/1.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.50/1.69       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.50/1.69  thf('33', plain,
% 1.50/1.69      (![X39 : $i, X40 : $i, X41 : $i]:
% 1.50/1.69         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 1.50/1.69          | ((k7_subset_1 @ X40 @ X39 @ X41) = (k4_xboole_0 @ X39 @ X41)))),
% 1.50/1.69      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.50/1.69  thf('34', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.50/1.69           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 1.50/1.69      inference('sup-', [status(thm)], ['32', '33'])).
% 1.50/1.69  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 1.50/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.69  thf('36', plain,
% 1.50/1.69      (((k2_tops_1 @ sk_A @ sk_B)
% 1.50/1.69         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.50/1.69            (k1_tops_1 @ sk_A @ sk_B)))),
% 1.50/1.69      inference('demod', [status(thm)], ['25', '26', '27', '34', '35'])).
% 1.50/1.69  thf('37', plain,
% 1.50/1.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.69  thf(t74_tops_1, axiom,
% 1.50/1.69    (![A:$i]:
% 1.50/1.69     ( ( l1_pre_topc @ A ) =>
% 1.50/1.69       ( ![B:$i]:
% 1.50/1.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.50/1.69           ( ( k1_tops_1 @ A @ B ) =
% 1.50/1.69             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.50/1.69  thf('38', plain,
% 1.50/1.69      (![X60 : $i, X61 : $i]:
% 1.50/1.69         (~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 1.50/1.69          | ((k1_tops_1 @ X61 @ X60)
% 1.50/1.69              = (k7_subset_1 @ (u1_struct_0 @ X61) @ X60 @ 
% 1.50/1.69                 (k2_tops_1 @ X61 @ X60)))
% 1.50/1.69          | ~ (l1_pre_topc @ X61))),
% 1.50/1.69      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.50/1.69  thf('39', plain,
% 1.50/1.69      ((~ (l1_pre_topc @ sk_A)
% 1.50/1.69        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.50/1.69            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.50/1.69               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.50/1.69      inference('sup-', [status(thm)], ['37', '38'])).
% 1.50/1.69  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 1.50/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.69  thf('41', plain,
% 1.50/1.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.69  thf('42', plain,
% 1.50/1.69      (![X39 : $i, X40 : $i, X41 : $i]:
% 1.50/1.69         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40))
% 1.50/1.69          | ((k7_subset_1 @ X40 @ X39 @ X41) = (k4_xboole_0 @ X39 @ X41)))),
% 1.50/1.69      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.50/1.69  thf('43', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.50/1.69           = (k4_xboole_0 @ sk_B @ X0))),
% 1.50/1.69      inference('sup-', [status(thm)], ['41', '42'])).
% 1.50/1.69  thf('44', plain,
% 1.50/1.69      (((k1_tops_1 @ sk_A @ sk_B)
% 1.50/1.69         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.50/1.69      inference('demod', [status(thm)], ['39', '40', '43'])).
% 1.50/1.69  thf('45', plain,
% 1.50/1.69      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 1.50/1.69      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.50/1.69  thf(d10_xboole_0, axiom,
% 1.50/1.69    (![A:$i,B:$i]:
% 1.50/1.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.50/1.69  thf('46', plain,
% 1.50/1.69      (![X1 : $i, X3 : $i]:
% 1.50/1.69         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 1.50/1.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.50/1.69  thf('47', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.50/1.69          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 1.50/1.69      inference('sup-', [status(thm)], ['45', '46'])).
% 1.50/1.69  thf('48', plain,
% 1.50/1.69      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.50/1.69        | ((sk_B) = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 1.50/1.69      inference('sup-', [status(thm)], ['44', '47'])).
% 1.50/1.69  thf('49', plain,
% 1.50/1.69      (((k1_tops_1 @ sk_A @ sk_B)
% 1.50/1.69         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.50/1.69      inference('demod', [status(thm)], ['39', '40', '43'])).
% 1.50/1.69  thf('50', plain,
% 1.50/1.69      ((~ (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.50/1.69        | ((sk_B) = (k1_tops_1 @ sk_A @ sk_B)))),
% 1.50/1.69      inference('demod', [status(thm)], ['48', '49'])).
% 1.50/1.69  thf('51', plain,
% 1.50/1.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.69  thf('52', plain,
% 1.50/1.69      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 1.50/1.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.50/1.69  thf('53', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 1.50/1.69      inference('simplify', [status(thm)], ['52'])).
% 1.50/1.69  thf('54', plain,
% 1.50/1.69      (![X44 : $i, X46 : $i]:
% 1.50/1.69         ((m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X46)) | ~ (r1_tarski @ X44 @ X46))),
% 1.50/1.69      inference('cnf', [status(esa)], [t3_subset])).
% 1.50/1.69  thf('55', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.50/1.69      inference('sup-', [status(thm)], ['53', '54'])).
% 1.50/1.69  thf(d5_subset_1, axiom,
% 1.50/1.69    (![A:$i,B:$i]:
% 1.50/1.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.50/1.69       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.50/1.69  thf('56', plain,
% 1.50/1.69      (![X24 : $i, X25 : $i]:
% 1.50/1.69         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 1.50/1.69          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 1.50/1.69      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.50/1.69  thf('57', plain,
% 1.50/1.69      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.50/1.69      inference('sup-', [status(thm)], ['55', '56'])).
% 1.50/1.69  thf(t3_boole, axiom,
% 1.50/1.69    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.50/1.69  thf('58', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 1.50/1.69      inference('cnf', [status(esa)], [t3_boole])).
% 1.50/1.69  thf('59', plain,
% 1.50/1.69      (![X17 : $i, X18 : $i]:
% 1.50/1.69         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.50/1.69           = (k1_setfam_1 @ (k2_tarski @ X17 @ X18)))),
% 1.50/1.69      inference('demod', [status(thm)], ['13', '14'])).
% 1.50/1.69  thf('60', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         ((k4_xboole_0 @ X0 @ X0)
% 1.50/1.69           = (k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)))),
% 1.50/1.69      inference('sup+', [status(thm)], ['58', '59'])).
% 1.50/1.69  thf('61', plain,
% 1.50/1.69      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.50/1.69      inference('sup-', [status(thm)], ['55', '56'])).
% 1.50/1.69  thf(t2_boole, axiom,
% 1.50/1.69    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.50/1.69  thf('62', plain,
% 1.50/1.69      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 1.50/1.69      inference('cnf', [status(esa)], [t2_boole])).
% 1.50/1.69  thf('63', plain,
% 1.50/1.69      (![X42 : $i, X43 : $i]:
% 1.50/1.69         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 1.50/1.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.50/1.69  thf('64', plain,
% 1.50/1.69      (![X8 : $i]:
% 1.50/1.69         ((k1_setfam_1 @ (k2_tarski @ X8 @ k1_xboole_0)) = (k1_xboole_0))),
% 1.50/1.69      inference('demod', [status(thm)], ['62', '63'])).
% 1.50/1.69  thf('65', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.50/1.69      inference('demod', [status(thm)], ['60', '61', '64'])).
% 1.50/1.69  thf('66', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 1.50/1.69      inference('demod', [status(thm)], ['57', '65'])).
% 1.50/1.69  thf('67', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.50/1.69      inference('sup-', [status(thm)], ['20', '21'])).
% 1.50/1.69  thf('68', plain,
% 1.50/1.69      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.50/1.69      inference('sup+', [status(thm)], ['66', '67'])).
% 1.50/1.69  thf('69', plain,
% 1.50/1.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.69  thf(dt_k4_subset_1, axiom,
% 1.50/1.69    (![A:$i,B:$i,C:$i]:
% 1.50/1.69     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.50/1.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.50/1.69       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.50/1.69  thf('70', plain,
% 1.50/1.69      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.50/1.69         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 1.50/1.69          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29))
% 1.50/1.69          | (m1_subset_1 @ (k4_subset_1 @ X29 @ X28 @ X30) @ 
% 1.50/1.69             (k1_zfmisc_1 @ X29)))),
% 1.50/1.69      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 1.50/1.69  thf('71', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 1.50/1.69           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.50/1.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.50/1.69      inference('sup-', [status(thm)], ['69', '70'])).
% 1.50/1.69  thf('72', plain,
% 1.50/1.69      ((m1_subset_1 @ 
% 1.50/1.69        (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ k1_xboole_0) @ 
% 1.50/1.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.69      inference('sup-', [status(thm)], ['68', '71'])).
% 1.50/1.69  thf('73', plain,
% 1.50/1.69      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.50/1.69      inference('sup+', [status(thm)], ['66', '67'])).
% 1.50/1.69  thf('74', plain,
% 1.50/1.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.69  thf(redefinition_k4_subset_1, axiom,
% 1.50/1.69    (![A:$i,B:$i,C:$i]:
% 1.50/1.69     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.50/1.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.50/1.69       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.50/1.69  thf('75', plain,
% 1.50/1.69      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.50/1.69         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 1.50/1.69          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37))
% 1.50/1.69          | ((k4_subset_1 @ X37 @ X36 @ X38) = (k2_xboole_0 @ X36 @ X38)))),
% 1.50/1.69      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.50/1.69  thf('76', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.50/1.69            = (k2_xboole_0 @ sk_B @ X0))
% 1.50/1.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.50/1.69      inference('sup-', [status(thm)], ['74', '75'])).
% 1.50/1.69  thf('77', plain,
% 1.50/1.69      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ k1_xboole_0)
% 1.50/1.69         = (k2_xboole_0 @ sk_B @ k1_xboole_0))),
% 1.50/1.69      inference('sup-', [status(thm)], ['73', '76'])).
% 1.50/1.69  thf('78', plain,
% 1.50/1.69      ((m1_subset_1 @ (k2_xboole_0 @ sk_B @ k1_xboole_0) @ 
% 1.50/1.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.69      inference('demod', [status(thm)], ['72', '77'])).
% 1.50/1.69  thf(t56_tops_1, axiom,
% 1.50/1.69    (![A:$i]:
% 1.50/1.69     ( ( l1_pre_topc @ A ) =>
% 1.50/1.69       ( ![B:$i]:
% 1.50/1.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.50/1.69           ( ![C:$i]:
% 1.50/1.69             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.50/1.69               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 1.50/1.69                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.50/1.69  thf('79', plain,
% 1.50/1.69      (![X53 : $i, X54 : $i, X55 : $i]:
% 1.50/1.69         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 1.50/1.69          | ~ (v3_pre_topc @ X53 @ X54)
% 1.50/1.69          | ~ (r1_tarski @ X53 @ X55)
% 1.50/1.69          | (r1_tarski @ X53 @ (k1_tops_1 @ X54 @ X55))
% 1.50/1.69          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 1.50/1.69          | ~ (l1_pre_topc @ X54))),
% 1.50/1.69      inference('cnf', [status(esa)], [t56_tops_1])).
% 1.50/1.69  thf('80', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         (~ (l1_pre_topc @ sk_A)
% 1.50/1.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.50/1.69          | (r1_tarski @ (k2_xboole_0 @ sk_B @ k1_xboole_0) @ 
% 1.50/1.69             (k1_tops_1 @ sk_A @ X0))
% 1.50/1.69          | ~ (r1_tarski @ (k2_xboole_0 @ sk_B @ k1_xboole_0) @ X0)
% 1.50/1.69          | ~ (v3_pre_topc @ (k2_xboole_0 @ sk_B @ k1_xboole_0) @ sk_A))),
% 1.50/1.69      inference('sup-', [status(thm)], ['78', '79'])).
% 1.50/1.69  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 1.50/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.69  thf('82', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.50/1.69          | (r1_tarski @ (k2_xboole_0 @ sk_B @ k1_xboole_0) @ 
% 1.50/1.69             (k1_tops_1 @ sk_A @ X0))
% 1.50/1.69          | ~ (r1_tarski @ (k2_xboole_0 @ sk_B @ k1_xboole_0) @ X0)
% 1.50/1.69          | ~ (v3_pre_topc @ (k2_xboole_0 @ sk_B @ k1_xboole_0) @ sk_A))),
% 1.50/1.69      inference('demod', [status(thm)], ['80', '81'])).
% 1.50/1.69  thf('83', plain,
% 1.50/1.69      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.50/1.69      inference('sup+', [status(thm)], ['66', '67'])).
% 1.50/1.69  thf('84', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.50/1.69      inference('sup-', [status(thm)], ['53', '54'])).
% 1.50/1.69  thf('85', plain,
% 1.50/1.69      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.50/1.69         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 1.50/1.69          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29))
% 1.50/1.69          | (m1_subset_1 @ (k4_subset_1 @ X29 @ X28 @ X30) @ 
% 1.50/1.69             (k1_zfmisc_1 @ X29)))),
% 1.50/1.69      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 1.50/1.69  thf('86', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         ((m1_subset_1 @ (k4_subset_1 @ X0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 1.50/1.69          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.50/1.69      inference('sup-', [status(thm)], ['84', '85'])).
% 1.50/1.69  thf('87', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         (m1_subset_1 @ (k4_subset_1 @ X0 @ X0 @ k1_xboole_0) @ 
% 1.50/1.69          (k1_zfmisc_1 @ X0))),
% 1.50/1.69      inference('sup-', [status(thm)], ['83', '86'])).
% 1.50/1.69  thf('88', plain,
% 1.50/1.69      (![X44 : $i, X45 : $i]:
% 1.50/1.69         ((r1_tarski @ X44 @ X45) | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45)))),
% 1.50/1.69      inference('cnf', [status(esa)], [t3_subset])).
% 1.50/1.69  thf('89', plain,
% 1.50/1.69      (![X0 : $i]: (r1_tarski @ (k4_subset_1 @ X0 @ X0 @ k1_xboole_0) @ X0)),
% 1.50/1.69      inference('sup-', [status(thm)], ['87', '88'])).
% 1.50/1.69  thf('90', plain,
% 1.50/1.69      (![X1 : $i, X3 : $i]:
% 1.50/1.69         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 1.50/1.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.50/1.69  thf('91', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         (~ (r1_tarski @ X0 @ (k4_subset_1 @ X0 @ X0 @ k1_xboole_0))
% 1.50/1.69          | ((X0) = (k4_subset_1 @ X0 @ X0 @ k1_xboole_0)))),
% 1.50/1.69      inference('sup-', [status(thm)], ['89', '90'])).
% 1.50/1.69  thf('92', plain,
% 1.50/1.69      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.50/1.69      inference('sup+', [status(thm)], ['66', '67'])).
% 1.50/1.69  thf('93', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.50/1.69      inference('sup-', [status(thm)], ['53', '54'])).
% 1.50/1.69  thf('94', plain,
% 1.50/1.69      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.50/1.69         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 1.50/1.69          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37))
% 1.50/1.69          | ((k4_subset_1 @ X37 @ X36 @ X38) = (k2_xboole_0 @ X36 @ X38)))),
% 1.50/1.69      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.50/1.69  thf('95', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         (((k4_subset_1 @ X0 @ X0 @ X1) = (k2_xboole_0 @ X0 @ X1))
% 1.50/1.69          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.50/1.69      inference('sup-', [status(thm)], ['93', '94'])).
% 1.50/1.69  thf('96', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         ((k4_subset_1 @ X0 @ X0 @ k1_xboole_0)
% 1.50/1.69           = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 1.50/1.69      inference('sup-', [status(thm)], ['92', '95'])).
% 1.50/1.69  thf('97', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 1.50/1.69      inference('demod', [status(thm)], ['57', '65'])).
% 1.50/1.69  thf(t41_xboole_1, axiom,
% 1.50/1.69    (![A:$i,B:$i,C:$i]:
% 1.50/1.69     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.50/1.69       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.50/1.69  thf('98', plain,
% 1.50/1.69      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.50/1.69         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 1.50/1.69           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 1.50/1.69      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.50/1.69  thf('99', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 1.50/1.69           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.50/1.69      inference('sup+', [status(thm)], ['97', '98'])).
% 1.50/1.69  thf('100', plain,
% 1.50/1.69      (![X22 : $i, X23 : $i]:
% 1.50/1.69         ((k2_tarski @ X23 @ X22) = (k2_tarski @ X22 @ X23))),
% 1.50/1.69      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.50/1.69  thf('101', plain,
% 1.50/1.69      (![X8 : $i]:
% 1.50/1.69         ((k1_setfam_1 @ (k2_tarski @ X8 @ k1_xboole_0)) = (k1_xboole_0))),
% 1.50/1.69      inference('demod', [status(thm)], ['62', '63'])).
% 1.50/1.69  thf('102', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         ((k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 1.50/1.69      inference('sup+', [status(thm)], ['100', '101'])).
% 1.50/1.69  thf('103', plain,
% 1.50/1.69      (![X4 : $i, X5 : $i]:
% 1.50/1.69         ((k4_xboole_0 @ X4 @ X5)
% 1.50/1.69           = (k5_xboole_0 @ X4 @ (k1_setfam_1 @ (k2_tarski @ X4 @ X5))))),
% 1.50/1.69      inference('demod', [status(thm)], ['8', '9'])).
% 1.50/1.69  thf('104', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 1.50/1.69           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 1.50/1.69      inference('sup+', [status(thm)], ['102', '103'])).
% 1.50/1.69  thf('105', plain,
% 1.50/1.69      (![X8 : $i]:
% 1.50/1.69         ((k1_setfam_1 @ (k2_tarski @ X8 @ k1_xboole_0)) = (k1_xboole_0))),
% 1.50/1.69      inference('demod', [status(thm)], ['62', '63'])).
% 1.50/1.69  thf('106', plain,
% 1.50/1.69      (![X4 : $i, X5 : $i]:
% 1.50/1.69         ((k4_xboole_0 @ X4 @ X5)
% 1.50/1.69           = (k5_xboole_0 @ X4 @ (k1_setfam_1 @ (k2_tarski @ X4 @ X5))))),
% 1.50/1.69      inference('demod', [status(thm)], ['8', '9'])).
% 1.50/1.69  thf('107', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.50/1.69      inference('sup+', [status(thm)], ['105', '106'])).
% 1.50/1.69  thf('108', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 1.50/1.69      inference('cnf', [status(esa)], [t3_boole])).
% 1.50/1.69  thf('109', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.50/1.69      inference('sup+', [status(thm)], ['107', '108'])).
% 1.50/1.69  thf('110', plain,
% 1.50/1.69      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.50/1.69      inference('demod', [status(thm)], ['104', '109'])).
% 1.50/1.69  thf('111', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.50/1.69      inference('demod', [status(thm)], ['99', '110'])).
% 1.50/1.69  thf('112', plain,
% 1.50/1.69      (![X17 : $i, X18 : $i]:
% 1.50/1.69         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.50/1.69           = (k1_setfam_1 @ (k2_tarski @ X17 @ X18)))),
% 1.50/1.69      inference('demod', [status(thm)], ['13', '14'])).
% 1.50/1.69  thf('113', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 1.50/1.69           = (k1_setfam_1 @ (k2_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))))),
% 1.50/1.69      inference('sup+', [status(thm)], ['111', '112'])).
% 1.50/1.69  thf('114', plain, (![X11 : $i]: ((k4_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 1.50/1.69      inference('cnf', [status(esa)], [t3_boole])).
% 1.50/1.69  thf('115', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         ((X1) = (k1_setfam_1 @ (k2_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))))),
% 1.50/1.69      inference('demod', [status(thm)], ['113', '114'])).
% 1.50/1.69  thf('116', plain,
% 1.50/1.69      (![X22 : $i, X23 : $i]:
% 1.50/1.69         ((k2_tarski @ X23 @ X22) = (k2_tarski @ X22 @ X23))),
% 1.50/1.69      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.50/1.69  thf('117', plain,
% 1.50/1.69      (![X17 : $i, X18 : $i]:
% 1.50/1.69         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 1.50/1.69           = (k1_setfam_1 @ (k2_tarski @ X17 @ X18)))),
% 1.50/1.69      inference('demod', [status(thm)], ['13', '14'])).
% 1.50/1.69  thf('118', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.50/1.69      inference('sup-', [status(thm)], ['20', '21'])).
% 1.50/1.69  thf('119', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 1.50/1.69          (k1_zfmisc_1 @ X1))),
% 1.50/1.69      inference('sup+', [status(thm)], ['117', '118'])).
% 1.50/1.69  thf('120', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         (m1_subset_1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 1.50/1.69          (k1_zfmisc_1 @ X0))),
% 1.50/1.69      inference('sup+', [status(thm)], ['116', '119'])).
% 1.50/1.69  thf('121', plain,
% 1.50/1.69      (![X44 : $i, X45 : $i]:
% 1.50/1.69         ((r1_tarski @ X44 @ X45) | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45)))),
% 1.50/1.69      inference('cnf', [status(esa)], [t3_subset])).
% 1.50/1.69  thf('122', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         (r1_tarski @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ X0)),
% 1.50/1.69      inference('sup-', [status(thm)], ['120', '121'])).
% 1.50/1.69  thf('123', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 1.50/1.69      inference('sup+', [status(thm)], ['115', '122'])).
% 1.50/1.69  thf('124', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         ((k4_subset_1 @ X0 @ X0 @ k1_xboole_0)
% 1.50/1.69           = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 1.50/1.69      inference('sup-', [status(thm)], ['92', '95'])).
% 1.50/1.69  thf('125', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 1.50/1.69      inference('demod', [status(thm)], ['91', '96', '123', '124'])).
% 1.50/1.69  thf('126', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 1.50/1.69      inference('demod', [status(thm)], ['91', '96', '123', '124'])).
% 1.50/1.69  thf('127', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 1.50/1.69      inference('demod', [status(thm)], ['91', '96', '123', '124'])).
% 1.50/1.69  thf('128', plain,
% 1.50/1.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.50/1.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.50/1.69             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.50/1.69        | (v3_pre_topc @ sk_B @ sk_A))),
% 1.50/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.69  thf('129', plain,
% 1.50/1.69      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 1.50/1.69      inference('split', [status(esa)], ['128'])).
% 1.50/1.69  thf('130', plain,
% 1.50/1.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.50/1.69          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.50/1.69              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 1.50/1.69        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 1.50/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.69  thf('131', plain,
% 1.50/1.69      (~
% 1.50/1.69       (((k2_tops_1 @ sk_A @ sk_B)
% 1.50/1.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.50/1.69             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 1.50/1.69       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 1.50/1.69      inference('split', [status(esa)], ['130'])).
% 1.50/1.69  thf('132', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.50/1.69           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 1.50/1.69      inference('sup-', [status(thm)], ['32', '33'])).
% 1.50/1.69  thf('133', plain,
% 1.50/1.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.50/1.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.50/1.69             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.50/1.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.50/1.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.50/1.69                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.50/1.69      inference('split', [status(esa)], ['128'])).
% 1.50/1.69  thf('134', plain,
% 1.50/1.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.50/1.69          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.50/1.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.50/1.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.50/1.69                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.50/1.69      inference('sup+', [status(thm)], ['132', '133'])).
% 1.50/1.69  thf(idempotence_k3_xboole_0, axiom,
% 1.50/1.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.50/1.69  thf('135', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.50/1.69      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.50/1.69  thf('136', plain,
% 1.50/1.69      (![X42 : $i, X43 : $i]:
% 1.50/1.69         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 1.50/1.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.50/1.69  thf('137', plain,
% 1.50/1.69      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 1.50/1.69      inference('demod', [status(thm)], ['135', '136'])).
% 1.50/1.69  thf('138', plain,
% 1.50/1.69      (![X4 : $i, X5 : $i]:
% 1.50/1.69         ((k4_xboole_0 @ X4 @ X5)
% 1.50/1.69           = (k5_xboole_0 @ X4 @ (k1_setfam_1 @ (k2_tarski @ X4 @ X5))))),
% 1.50/1.69      inference('demod', [status(thm)], ['8', '9'])).
% 1.50/1.69  thf('139', plain,
% 1.50/1.69      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.50/1.69      inference('sup+', [status(thm)], ['137', '138'])).
% 1.50/1.69  thf(t49_xboole_1, axiom,
% 1.50/1.69    (![A:$i,B:$i,C:$i]:
% 1.50/1.69     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.50/1.69       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 1.50/1.69  thf('140', plain,
% 1.50/1.69      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.50/1.69         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 1.50/1.69           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21))),
% 1.50/1.69      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.50/1.69  thf('141', plain,
% 1.50/1.69      (![X42 : $i, X43 : $i]:
% 1.50/1.69         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 1.50/1.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.50/1.69  thf('142', plain,
% 1.50/1.69      (![X42 : $i, X43 : $i]:
% 1.50/1.69         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 1.50/1.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.50/1.69  thf('143', plain,
% 1.50/1.69      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.50/1.69         ((k1_setfam_1 @ (k2_tarski @ X19 @ (k4_xboole_0 @ X20 @ X21)))
% 1.50/1.69           = (k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X19 @ X20)) @ X21))),
% 1.50/1.69      inference('demod', [status(thm)], ['140', '141', '142'])).
% 1.50/1.69  thf('144', plain,
% 1.50/1.69      (![X4 : $i, X5 : $i]:
% 1.50/1.69         ((k4_xboole_0 @ X4 @ X5)
% 1.50/1.69           = (k5_xboole_0 @ X4 @ (k1_setfam_1 @ (k2_tarski @ X4 @ X5))))),
% 1.50/1.69      inference('demod', [status(thm)], ['8', '9'])).
% 1.50/1.69  thf('145', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.69         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 1.50/1.69           = (k5_xboole_0 @ X2 @ 
% 1.50/1.69              (k4_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X2 @ X1)) @ X0)))),
% 1.50/1.69      inference('sup+', [status(thm)], ['143', '144'])).
% 1.50/1.69  thf('146', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         ((k4_xboole_0 @ X1 @ 
% 1.50/1.69           (k4_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))
% 1.50/1.69           = (k5_xboole_0 @ X1 @ 
% 1.50/1.69              (k5_xboole_0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)) @ 
% 1.50/1.69               (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))))),
% 1.50/1.69      inference('sup+', [status(thm)], ['139', '145'])).
% 1.50/1.69  thf('147', plain,
% 1.50/1.69      (![X22 : $i, X23 : $i]:
% 1.50/1.69         ((k2_tarski @ X23 @ X22) = (k2_tarski @ X22 @ X23))),
% 1.50/1.69      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.50/1.69  thf(t47_xboole_1, axiom,
% 1.50/1.69    (![A:$i,B:$i]:
% 1.50/1.69     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.50/1.69  thf('148', plain,
% 1.50/1.69      (![X15 : $i, X16 : $i]:
% 1.50/1.69         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 1.50/1.69           = (k4_xboole_0 @ X15 @ X16))),
% 1.50/1.69      inference('cnf', [status(esa)], [t47_xboole_1])).
% 1.50/1.69  thf('149', plain,
% 1.50/1.69      (![X42 : $i, X43 : $i]:
% 1.50/1.69         ((k1_setfam_1 @ (k2_tarski @ X42 @ X43)) = (k3_xboole_0 @ X42 @ X43))),
% 1.50/1.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.50/1.69  thf('150', plain,
% 1.50/1.69      (![X15 : $i, X16 : $i]:
% 1.50/1.69         ((k4_xboole_0 @ X15 @ (k1_setfam_1 @ (k2_tarski @ X15 @ X16)))
% 1.50/1.69           = (k4_xboole_0 @ X15 @ X16))),
% 1.50/1.69      inference('demod', [status(thm)], ['148', '149'])).
% 1.50/1.69  thf('151', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         ((k4_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 1.50/1.69           = (k4_xboole_0 @ X0 @ X1))),
% 1.50/1.69      inference('sup+', [status(thm)], ['147', '150'])).
% 1.50/1.69  thf('152', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 1.50/1.69      inference('demod', [status(thm)], ['57', '65'])).
% 1.50/1.69  thf('153', plain,
% 1.50/1.69      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.50/1.69      inference('sup+', [status(thm)], ['137', '138'])).
% 1.50/1.69  thf('154', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 1.50/1.69      inference('sup+', [status(thm)], ['152', '153'])).
% 1.50/1.69  thf('155', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.50/1.69      inference('sup+', [status(thm)], ['107', '108'])).
% 1.50/1.69  thf('156', plain,
% 1.50/1.69      (![X0 : $i, X1 : $i]:
% 1.50/1.69         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)) = (X1))),
% 1.50/1.69      inference('demod', [status(thm)], ['146', '151', '154', '155'])).
% 1.50/1.69  thf('157', plain,
% 1.50/1.69      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 1.50/1.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.50/1.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.50/1.69                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.50/1.69      inference('sup+', [status(thm)], ['134', '156'])).
% 1.50/1.69  thf('158', plain,
% 1.50/1.69      (((k1_tops_1 @ sk_A @ sk_B)
% 1.50/1.69         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.50/1.69      inference('demod', [status(thm)], ['39', '40', '43'])).
% 1.50/1.69  thf('159', plain,
% 1.50/1.69      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 1.50/1.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.50/1.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.50/1.69                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.50/1.69      inference('sup+', [status(thm)], ['157', '158'])).
% 1.50/1.69  thf('160', plain,
% 1.50/1.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.50/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.69  thf(fc9_tops_1, axiom,
% 1.50/1.69    (![A:$i,B:$i]:
% 1.50/1.69     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.50/1.69         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.50/1.69       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 1.50/1.69  thf('161', plain,
% 1.50/1.69      (![X49 : $i, X50 : $i]:
% 1.50/1.69         (~ (l1_pre_topc @ X49)
% 1.50/1.69          | ~ (v2_pre_topc @ X49)
% 1.50/1.69          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 1.50/1.69          | (v3_pre_topc @ (k1_tops_1 @ X49 @ X50) @ X49))),
% 1.50/1.69      inference('cnf', [status(esa)], [fc9_tops_1])).
% 1.50/1.69  thf('162', plain,
% 1.50/1.69      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 1.50/1.69        | ~ (v2_pre_topc @ sk_A)
% 1.50/1.69        | ~ (l1_pre_topc @ sk_A))),
% 1.50/1.69      inference('sup-', [status(thm)], ['160', '161'])).
% 1.50/1.69  thf('163', plain, ((v2_pre_topc @ sk_A)),
% 1.50/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.69  thf('164', plain, ((l1_pre_topc @ sk_A)),
% 1.50/1.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.69  thf('165', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 1.50/1.69      inference('demod', [status(thm)], ['162', '163', '164'])).
% 1.50/1.69  thf('166', plain,
% 1.50/1.69      (((v3_pre_topc @ sk_B @ sk_A))
% 1.50/1.69         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.50/1.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.50/1.69                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.50/1.69      inference('sup+', [status(thm)], ['159', '165'])).
% 1.50/1.69  thf('167', plain,
% 1.50/1.69      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 1.50/1.69      inference('split', [status(esa)], ['130'])).
% 1.50/1.69  thf('168', plain,
% 1.50/1.69      (((v3_pre_topc @ sk_B @ sk_A)) | 
% 1.50/1.69       ~
% 1.50/1.69       (((k2_tops_1 @ sk_A @ sk_B)
% 1.50/1.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.50/1.69             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 1.50/1.69      inference('sup-', [status(thm)], ['166', '167'])).
% 1.50/1.69  thf('169', plain,
% 1.50/1.69      (((v3_pre_topc @ sk_B @ sk_A)) | 
% 1.50/1.69       (((k2_tops_1 @ sk_A @ sk_B)
% 1.50/1.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.50/1.69             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 1.50/1.69      inference('split', [status(esa)], ['128'])).
% 1.50/1.69  thf('170', plain, (((v3_pre_topc @ sk_B @ sk_A))),
% 1.50/1.69      inference('sat_resolution*', [status(thm)], ['131', '168', '169'])).
% 1.50/1.69  thf('171', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 1.50/1.69      inference('simpl_trail', [status(thm)], ['129', '170'])).
% 1.50/1.69  thf('172', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.50/1.69          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 1.50/1.69          | ~ (r1_tarski @ sk_B @ X0))),
% 1.50/1.69      inference('demod', [status(thm)], ['82', '125', '126', '127', '171'])).
% 1.50/1.69  thf('173', plain,
% 1.50/1.69      ((~ (r1_tarski @ sk_B @ sk_B)
% 1.50/1.69        | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.50/1.69      inference('sup-', [status(thm)], ['51', '172'])).
% 1.50/1.69  thf('174', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 1.50/1.69      inference('simplify', [status(thm)], ['52'])).
% 1.50/1.69  thf('175', plain, ((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))),
% 1.50/1.69      inference('demod', [status(thm)], ['173', '174'])).
% 1.50/1.69  thf('176', plain, (((sk_B) = (k1_tops_1 @ sk_A @ sk_B))),
% 1.50/1.69      inference('demod', [status(thm)], ['50', '175'])).
% 1.50/1.69  thf('177', plain,
% 1.50/1.69      (((k2_tops_1 @ sk_A @ sk_B)
% 1.50/1.69         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 1.50/1.69      inference('demod', [status(thm)], ['36', '176'])).
% 1.50/1.69  thf('178', plain,
% 1.50/1.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.50/1.69          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.50/1.69              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.50/1.69         <= (~
% 1.50/1.69             (((k2_tops_1 @ sk_A @ sk_B)
% 1.50/1.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.50/1.69                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.50/1.69      inference('split', [status(esa)], ['130'])).
% 1.50/1.69  thf('179', plain,
% 1.50/1.69      (![X0 : $i]:
% 1.50/1.69         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.50/1.69           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 1.50/1.69      inference('sup-', [status(thm)], ['32', '33'])).
% 1.50/1.69  thf('180', plain,
% 1.50/1.69      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.50/1.69          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 1.50/1.69         <= (~
% 1.50/1.69             (((k2_tops_1 @ sk_A @ sk_B)
% 1.50/1.69                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.50/1.69                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 1.50/1.69      inference('demod', [status(thm)], ['178', '179'])).
% 1.50/1.69  thf('181', plain,
% 1.50/1.69      (~
% 1.50/1.69       (((k2_tops_1 @ sk_A @ sk_B)
% 1.50/1.69          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.50/1.69             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 1.50/1.69      inference('sat_resolution*', [status(thm)], ['131', '168'])).
% 1.50/1.69  thf('182', plain,
% 1.50/1.69      (((k2_tops_1 @ sk_A @ sk_B)
% 1.50/1.69         != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 1.50/1.69      inference('simpl_trail', [status(thm)], ['180', '181'])).
% 1.50/1.69  thf('183', plain, ($false),
% 1.50/1.69      inference('simplify_reflect-', [status(thm)], ['177', '182'])).
% 1.50/1.69  
% 1.50/1.69  % SZS output end Refutation
% 1.50/1.69  
% 1.50/1.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
