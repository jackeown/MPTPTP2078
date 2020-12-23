%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9JpGUZsgoE

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:12 EST 2020

% Result     : Theorem 24.51s
% Output     : Refutation 24.51s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 181 expanded)
%              Number of leaves         :   33 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :  734 (1514 expanded)
%              Number of equality atoms :   47 (  90 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t69_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t69_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X54: $i,X55: $i] :
      ( ( r1_tarski @ X54 @ X55 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ X55 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('6',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_tarski @ X33 @ X32 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X52 @ X53 ) )
      = ( k3_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X52 @ X53 ) )
      = ( k3_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X28 @ ( k4_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf('18',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('20',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( l1_pre_topc @ X57 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X57 @ X58 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('21',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('25',plain,(
    ! [X54: $i,X56: $i] :
      ( ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ X56 ) )
      | ~ ( r1_tarski @ X54 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X44 ) )
      | ( ( k4_subset_1 @ X44 @ X43 @ X45 )
        = ( k2_xboole_0 @ X43 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['18','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('34',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X65 ) ) )
      | ( ( k2_pre_topc @ X65 @ X64 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X65 ) @ X64 @ ( k2_tops_1 @ X65 @ X64 ) ) )
      | ~ ( l1_pre_topc @ X65 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('40',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','37','38','39'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('41',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('42',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v4_pre_topc @ B @ A )
                  & ( r1_tarski @ C @ B ) )
               => ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) )).

thf('47',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ~ ( v4_pre_topc @ X59 @ X60 )
      | ~ ( r1_tarski @ X61 @ X59 )
      | ( r1_tarski @ ( k2_pre_topc @ X60 @ X61 ) @ X59 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ~ ( l1_pre_topc @ X60 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('54',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['52','54'])).

thf('56',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_xboole_0 @ X11 @ X10 )
        = X10 )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('57',plain,
    ( ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('59',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('62',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['0','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9JpGUZsgoE
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:06:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 24.51/24.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 24.51/24.69  % Solved by: fo/fo7.sh
% 24.51/24.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 24.51/24.69  % done 27746 iterations in 24.221s
% 24.51/24.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 24.51/24.69  % SZS output start Refutation
% 24.51/24.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 24.51/24.69  thf(sk_B_type, type, sk_B: $i).
% 24.51/24.69  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 24.51/24.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 24.51/24.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 24.51/24.69  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 24.51/24.69  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 24.51/24.69  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 24.51/24.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 24.51/24.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 24.51/24.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 24.51/24.69  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 24.51/24.69  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 24.51/24.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 24.51/24.69  thf(sk_A_type, type, sk_A: $i).
% 24.51/24.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 24.51/24.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 24.51/24.69  thf(t69_tops_1, conjecture,
% 24.51/24.69    (![A:$i]:
% 24.51/24.69     ( ( l1_pre_topc @ A ) =>
% 24.51/24.69       ( ![B:$i]:
% 24.51/24.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 24.51/24.69           ( ( v4_pre_topc @ B @ A ) =>
% 24.51/24.69             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 24.51/24.69  thf(zf_stmt_0, negated_conjecture,
% 24.51/24.69    (~( ![A:$i]:
% 24.51/24.69        ( ( l1_pre_topc @ A ) =>
% 24.51/24.69          ( ![B:$i]:
% 24.51/24.69            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 24.51/24.69              ( ( v4_pre_topc @ B @ A ) =>
% 24.51/24.69                ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ) )),
% 24.51/24.69    inference('cnf.neg', [status(esa)], [t69_tops_1])).
% 24.51/24.69  thf('0', plain, (~ (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 24.51/24.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.51/24.69  thf('1', plain,
% 24.51/24.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.51/24.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.51/24.69  thf(t3_subset, axiom,
% 24.51/24.69    (![A:$i,B:$i]:
% 24.51/24.69     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 24.51/24.69  thf('2', plain,
% 24.51/24.69      (![X54 : $i, X55 : $i]:
% 24.51/24.69         ((r1_tarski @ X54 @ X55) | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ X55)))),
% 24.51/24.69      inference('cnf', [status(esa)], [t3_subset])).
% 24.51/24.69  thf('3', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 24.51/24.69      inference('sup-', [status(thm)], ['1', '2'])).
% 24.51/24.69  thf(t28_xboole_1, axiom,
% 24.51/24.69    (![A:$i,B:$i]:
% 24.51/24.69     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 24.51/24.69  thf('4', plain,
% 24.51/24.69      (![X17 : $i, X18 : $i]:
% 24.51/24.69         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 24.51/24.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 24.51/24.69  thf('5', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 24.51/24.69      inference('sup-', [status(thm)], ['3', '4'])).
% 24.51/24.69  thf(commutativity_k2_tarski, axiom,
% 24.51/24.69    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 24.51/24.69  thf('6', plain,
% 24.51/24.69      (![X32 : $i, X33 : $i]:
% 24.51/24.69         ((k2_tarski @ X33 @ X32) = (k2_tarski @ X32 @ X33))),
% 24.51/24.69      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 24.51/24.69  thf(t12_setfam_1, axiom,
% 24.51/24.69    (![A:$i,B:$i]:
% 24.51/24.69     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 24.51/24.69  thf('7', plain,
% 24.51/24.69      (![X52 : $i, X53 : $i]:
% 24.51/24.69         ((k1_setfam_1 @ (k2_tarski @ X52 @ X53)) = (k3_xboole_0 @ X52 @ X53))),
% 24.51/24.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 24.51/24.69  thf('8', plain,
% 24.51/24.69      (![X0 : $i, X1 : $i]:
% 24.51/24.69         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 24.51/24.69      inference('sup+', [status(thm)], ['6', '7'])).
% 24.51/24.69  thf('9', plain,
% 24.51/24.69      (![X52 : $i, X53 : $i]:
% 24.51/24.69         ((k1_setfam_1 @ (k2_tarski @ X52 @ X53)) = (k3_xboole_0 @ X52 @ X53))),
% 24.51/24.69      inference('cnf', [status(esa)], [t12_setfam_1])).
% 24.51/24.69  thf('10', plain,
% 24.51/24.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 24.51/24.69      inference('sup+', [status(thm)], ['8', '9'])).
% 24.51/24.69  thf(t100_xboole_1, axiom,
% 24.51/24.69    (![A:$i,B:$i]:
% 24.51/24.69     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 24.51/24.69  thf('11', plain,
% 24.51/24.69      (![X8 : $i, X9 : $i]:
% 24.51/24.69         ((k4_xboole_0 @ X8 @ X9)
% 24.51/24.69           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 24.51/24.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 24.51/24.69  thf('12', plain,
% 24.51/24.69      (![X0 : $i, X1 : $i]:
% 24.51/24.69         ((k4_xboole_0 @ X0 @ X1)
% 24.51/24.69           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 24.51/24.69      inference('sup+', [status(thm)], ['10', '11'])).
% 24.51/24.69  thf('13', plain,
% 24.51/24.69      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 24.51/24.69         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 24.51/24.69      inference('sup+', [status(thm)], ['5', '12'])).
% 24.51/24.69  thf(t48_xboole_1, axiom,
% 24.51/24.69    (![A:$i,B:$i]:
% 24.51/24.69     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 24.51/24.69  thf('14', plain,
% 24.51/24.69      (![X28 : $i, X29 : $i]:
% 24.51/24.69         ((k4_xboole_0 @ X28 @ (k4_xboole_0 @ X28 @ X29))
% 24.51/24.69           = (k3_xboole_0 @ X28 @ X29))),
% 24.51/24.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 24.51/24.69  thf('15', plain,
% 24.51/24.69      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 24.51/24.69         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 24.51/24.69         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 24.51/24.69      inference('sup+', [status(thm)], ['13', '14'])).
% 24.51/24.69  thf('16', plain,
% 24.51/24.69      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 24.51/24.69      inference('sup+', [status(thm)], ['8', '9'])).
% 24.51/24.69  thf('17', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 24.51/24.69      inference('sup-', [status(thm)], ['3', '4'])).
% 24.51/24.69  thf('18', plain,
% 24.51/24.69      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 24.51/24.69         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 24.51/24.69      inference('demod', [status(thm)], ['15', '16', '17'])).
% 24.51/24.69  thf('19', plain,
% 24.51/24.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.51/24.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.51/24.69  thf(dt_k2_tops_1, axiom,
% 24.51/24.69    (![A:$i,B:$i]:
% 24.51/24.69     ( ( ( l1_pre_topc @ A ) & 
% 24.51/24.69         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 24.51/24.69       ( m1_subset_1 @
% 24.51/24.69         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 24.51/24.69  thf('20', plain,
% 24.51/24.69      (![X57 : $i, X58 : $i]:
% 24.51/24.69         (~ (l1_pre_topc @ X57)
% 24.51/24.69          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 24.51/24.69          | (m1_subset_1 @ (k2_tops_1 @ X57 @ X58) @ 
% 24.51/24.69             (k1_zfmisc_1 @ (u1_struct_0 @ X57))))),
% 24.51/24.69      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 24.51/24.69  thf('21', plain,
% 24.51/24.69      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 24.51/24.69         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 24.51/24.69        | ~ (l1_pre_topc @ sk_A))),
% 24.51/24.69      inference('sup-', [status(thm)], ['19', '20'])).
% 24.51/24.69  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 24.51/24.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.51/24.69  thf('23', plain,
% 24.51/24.69      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 24.51/24.69        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.51/24.69      inference('demod', [status(thm)], ['21', '22'])).
% 24.51/24.69  thf(t36_xboole_1, axiom,
% 24.51/24.69    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 24.51/24.69  thf('24', plain,
% 24.51/24.69      (![X20 : $i, X21 : $i]: (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X20)),
% 24.51/24.69      inference('cnf', [status(esa)], [t36_xboole_1])).
% 24.51/24.69  thf('25', plain,
% 24.51/24.69      (![X54 : $i, X56 : $i]:
% 24.51/24.69         ((m1_subset_1 @ X54 @ (k1_zfmisc_1 @ X56)) | ~ (r1_tarski @ X54 @ X56))),
% 24.51/24.69      inference('cnf', [status(esa)], [t3_subset])).
% 24.51/24.69  thf('26', plain,
% 24.51/24.69      (![X0 : $i, X1 : $i]:
% 24.51/24.69         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 24.51/24.69      inference('sup-', [status(thm)], ['24', '25'])).
% 24.51/24.69  thf(redefinition_k4_subset_1, axiom,
% 24.51/24.69    (![A:$i,B:$i,C:$i]:
% 24.51/24.69     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 24.51/24.69         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 24.51/24.69       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 24.51/24.69  thf('27', plain,
% 24.51/24.69      (![X43 : $i, X44 : $i, X45 : $i]:
% 24.51/24.69         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 24.51/24.69          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X44))
% 24.51/24.69          | ((k4_subset_1 @ X44 @ X43 @ X45) = (k2_xboole_0 @ X43 @ X45)))),
% 24.51/24.69      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 24.51/24.69  thf('28', plain,
% 24.51/24.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 24.51/24.69         (((k4_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 24.51/24.69            = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))
% 24.51/24.69          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0)))),
% 24.51/24.69      inference('sup-', [status(thm)], ['26', '27'])).
% 24.51/24.69  thf('29', plain,
% 24.51/24.69      (![X0 : $i]:
% 24.51/24.69         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.51/24.69           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 24.51/24.69           (k2_tops_1 @ sk_A @ sk_B))
% 24.51/24.69           = (k2_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 24.51/24.69              (k2_tops_1 @ sk_A @ sk_B)))),
% 24.51/24.69      inference('sup-', [status(thm)], ['23', '28'])).
% 24.51/24.69  thf(commutativity_k2_xboole_0, axiom,
% 24.51/24.69    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 24.51/24.69  thf('30', plain,
% 24.51/24.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 24.51/24.69      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 24.51/24.69  thf('31', plain,
% 24.51/24.69      (![X0 : $i]:
% 24.51/24.69         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 24.51/24.69           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 24.51/24.69           (k2_tops_1 @ sk_A @ sk_B))
% 24.51/24.69           = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 24.51/24.69              (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 24.51/24.69      inference('demod', [status(thm)], ['29', '30'])).
% 24.51/24.69  thf('32', plain,
% 24.51/24.69      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 24.51/24.69         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 24.51/24.69            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 24.51/24.69             (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 24.51/24.69      inference('sup+', [status(thm)], ['18', '31'])).
% 24.51/24.69  thf('33', plain,
% 24.51/24.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.51/24.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.51/24.69  thf(t65_tops_1, axiom,
% 24.51/24.69    (![A:$i]:
% 24.51/24.69     ( ( l1_pre_topc @ A ) =>
% 24.51/24.69       ( ![B:$i]:
% 24.51/24.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 24.51/24.69           ( ( k2_pre_topc @ A @ B ) =
% 24.51/24.69             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 24.51/24.69  thf('34', plain,
% 24.51/24.69      (![X64 : $i, X65 : $i]:
% 24.51/24.69         (~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (u1_struct_0 @ X65)))
% 24.51/24.69          | ((k2_pre_topc @ X65 @ X64)
% 24.51/24.69              = (k4_subset_1 @ (u1_struct_0 @ X65) @ X64 @ 
% 24.51/24.69                 (k2_tops_1 @ X65 @ X64)))
% 24.51/24.69          | ~ (l1_pre_topc @ X65))),
% 24.51/24.69      inference('cnf', [status(esa)], [t65_tops_1])).
% 24.51/24.69  thf('35', plain,
% 24.51/24.69      ((~ (l1_pre_topc @ sk_A)
% 24.51/24.69        | ((k2_pre_topc @ sk_A @ sk_B)
% 24.51/24.69            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 24.51/24.69               (k2_tops_1 @ sk_A @ sk_B))))),
% 24.51/24.69      inference('sup-', [status(thm)], ['33', '34'])).
% 24.51/24.69  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 24.51/24.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.51/24.69  thf('37', plain,
% 24.51/24.69      (((k2_pre_topc @ sk_A @ sk_B)
% 24.51/24.69         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 24.51/24.69            (k2_tops_1 @ sk_A @ sk_B)))),
% 24.51/24.69      inference('demod', [status(thm)], ['35', '36'])).
% 24.51/24.69  thf('38', plain,
% 24.51/24.69      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 24.51/24.69         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 24.51/24.69      inference('demod', [status(thm)], ['15', '16', '17'])).
% 24.51/24.69  thf('39', plain,
% 24.51/24.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 24.51/24.69      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 24.51/24.69  thf('40', plain,
% 24.51/24.69      (((k2_pre_topc @ sk_A @ sk_B)
% 24.51/24.69         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 24.51/24.69      inference('demod', [status(thm)], ['32', '37', '38', '39'])).
% 24.51/24.69  thf(t7_xboole_1, axiom,
% 24.51/24.69    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 24.51/24.69  thf('41', plain,
% 24.51/24.69      (![X30 : $i, X31 : $i]: (r1_tarski @ X30 @ (k2_xboole_0 @ X30 @ X31))),
% 24.51/24.69      inference('cnf', [status(esa)], [t7_xboole_1])).
% 24.51/24.69  thf(t12_xboole_1, axiom,
% 24.51/24.69    (![A:$i,B:$i]:
% 24.51/24.69     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 24.51/24.69  thf('42', plain,
% 24.51/24.69      (![X10 : $i, X11 : $i]:
% 24.51/24.69         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 24.51/24.69      inference('cnf', [status(esa)], [t12_xboole_1])).
% 24.51/24.69  thf('43', plain,
% 24.51/24.69      (![X0 : $i, X1 : $i]:
% 24.51/24.69         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 24.51/24.69           = (k2_xboole_0 @ X1 @ X0))),
% 24.51/24.69      inference('sup-', [status(thm)], ['41', '42'])).
% 24.51/24.69  thf('44', plain,
% 24.51/24.69      (((k2_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))
% 24.51/24.69         = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 24.51/24.69      inference('sup+', [status(thm)], ['40', '43'])).
% 24.51/24.69  thf('45', plain,
% 24.51/24.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.51/24.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.51/24.69  thf('46', plain,
% 24.51/24.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 24.51/24.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.51/24.69  thf(t31_tops_1, axiom,
% 24.51/24.69    (![A:$i]:
% 24.51/24.69     ( ( l1_pre_topc @ A ) =>
% 24.51/24.69       ( ![B:$i]:
% 24.51/24.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 24.51/24.69           ( ![C:$i]:
% 24.51/24.69             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 24.51/24.69               ( ( ( v4_pre_topc @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 24.51/24.69                 ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) ) ))).
% 24.51/24.69  thf('47', plain,
% 24.51/24.69      (![X59 : $i, X60 : $i, X61 : $i]:
% 24.51/24.69         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 24.51/24.69          | ~ (v4_pre_topc @ X59 @ X60)
% 24.51/24.69          | ~ (r1_tarski @ X61 @ X59)
% 24.51/24.69          | (r1_tarski @ (k2_pre_topc @ X60 @ X61) @ X59)
% 24.51/24.69          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 24.51/24.69          | ~ (l1_pre_topc @ X60))),
% 24.51/24.69      inference('cnf', [status(esa)], [t31_tops_1])).
% 24.51/24.69  thf('48', plain,
% 24.51/24.69      (![X0 : $i]:
% 24.51/24.69         (~ (l1_pre_topc @ sk_A)
% 24.51/24.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 24.51/24.69          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_B)
% 24.51/24.69          | ~ (r1_tarski @ X0 @ sk_B)
% 24.51/24.69          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 24.51/24.69      inference('sup-', [status(thm)], ['46', '47'])).
% 24.51/24.69  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 24.51/24.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.51/24.69  thf('50', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 24.51/24.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 24.51/24.69  thf('51', plain,
% 24.51/24.69      (![X0 : $i]:
% 24.51/24.69         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 24.51/24.69          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_B)
% 24.51/24.69          | ~ (r1_tarski @ X0 @ sk_B))),
% 24.51/24.69      inference('demod', [status(thm)], ['48', '49', '50'])).
% 24.51/24.69  thf('52', plain,
% 24.51/24.69      ((~ (r1_tarski @ sk_B @ sk_B)
% 24.51/24.69        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 24.51/24.69      inference('sup-', [status(thm)], ['45', '51'])).
% 24.51/24.69  thf(d10_xboole_0, axiom,
% 24.51/24.69    (![A:$i,B:$i]:
% 24.51/24.69     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 24.51/24.69  thf('53', plain,
% 24.51/24.69      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 24.51/24.69      inference('cnf', [status(esa)], [d10_xboole_0])).
% 24.51/24.69  thf('54', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 24.51/24.69      inference('simplify', [status(thm)], ['53'])).
% 24.51/24.69  thf('55', plain, ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)),
% 24.51/24.69      inference('demod', [status(thm)], ['52', '54'])).
% 24.51/24.69  thf('56', plain,
% 24.51/24.69      (![X10 : $i, X11 : $i]:
% 24.51/24.69         (((k2_xboole_0 @ X11 @ X10) = (X10)) | ~ (r1_tarski @ X11 @ X10))),
% 24.51/24.69      inference('cnf', [status(esa)], [t12_xboole_1])).
% 24.51/24.69  thf('57', plain,
% 24.51/24.69      (((k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B) = (sk_B))),
% 24.51/24.69      inference('sup-', [status(thm)], ['55', '56'])).
% 24.51/24.69  thf('58', plain,
% 24.51/24.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 24.51/24.69      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 24.51/24.69  thf('59', plain,
% 24.51/24.69      (((k2_xboole_0 @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 24.51/24.69      inference('demod', [status(thm)], ['57', '58'])).
% 24.51/24.69  thf('60', plain,
% 24.51/24.69      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 24.51/24.69      inference('demod', [status(thm)], ['44', '59'])).
% 24.51/24.69  thf('61', plain,
% 24.51/24.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 24.51/24.69      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 24.51/24.69  thf('62', plain,
% 24.51/24.69      (![X30 : $i, X31 : $i]: (r1_tarski @ X30 @ (k2_xboole_0 @ X30 @ X31))),
% 24.51/24.69      inference('cnf', [status(esa)], [t7_xboole_1])).
% 24.51/24.69  thf('63', plain,
% 24.51/24.69      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 24.51/24.69      inference('sup+', [status(thm)], ['61', '62'])).
% 24.51/24.69  thf('64', plain, ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 24.51/24.69      inference('sup+', [status(thm)], ['60', '63'])).
% 24.51/24.69  thf('65', plain, ($false), inference('demod', [status(thm)], ['0', '64'])).
% 24.51/24.69  
% 24.51/24.69  % SZS output end Refutation
% 24.51/24.69  
% 24.51/24.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
