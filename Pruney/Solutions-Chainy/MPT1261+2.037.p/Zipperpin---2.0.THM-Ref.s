%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.g6uZEiQUme

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:42 EST 2020

% Result     : Theorem 9.24s
% Output     : Refutation 9.24s
% Verified   : 
% Statistics : Number of formulae       :  384 (3508 expanded)
%              Number of leaves         :   50 (1144 expanded)
%              Depth                    :   28
%              Number of atoms          : 3520 (35365 expanded)
%              Number of equality atoms :  292 (2672 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('0',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_tarski @ X22 @ X21 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X23 @ X24 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

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

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r1_tarski @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','13'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      | ~ ( r1_tarski @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_tarski @ X22 @ X21 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X40 @ X41 ) )
      = ( k3_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('34',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('35',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('37',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( l1_pre_topc @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X47 @ X48 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X47 ) ) ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('42',plain,(
    ! [X42: $i,X44: $i] :
      ( ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( r1_tarski @ X42 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('44',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) )
      | ( ( k4_subset_1 @ X33 @ X32 @ X34 )
        = ( k2_xboole_0 @ X32 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['35','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('51',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ( ( k2_pre_topc @ X54 @ X53 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X54 ) @ X53 @ ( k2_tops_1 @ X54 @ X53 ) ) )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['55'])).

thf('57',plain,(
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

thf('58',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ~ ( v4_pre_topc @ X45 @ X46 )
      | ( ( k2_pre_topc @ X46 @ X45 )
        = X45 )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('66',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k4_subset_1 @ X38 @ X39 @ ( k3_subset_1 @ X38 @ X39 ) )
        = ( k2_subset_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('67',plain,(
    ! [X25: $i] :
      ( ( k2_subset_1 @ X25 )
      = X25 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('68',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k4_subset_1 @ X38 @ X39 @ ( k3_subset_1 @ X38 @ X39 ) )
        = X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('71',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['69','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('77',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('79',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( ( k7_subset_1 @ X36 @ X35 @ X37 )
        = ( k4_xboole_0 @ X35 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['55'])).

thf('82',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('84',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('86',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X42: $i,X44: $i] :
      ( ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( r1_tarski @ X42 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('90',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['77','90'])).

thf('92',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['76','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('94',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( k4_subset_1 @ sk_B @ ( k4_xboole_0 @ sk_B @ X1 ) @ ( k3_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ X1 ) @ ( k3_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['75','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('97',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( ( k1_tops_1 @ X56 @ X55 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X56 ) @ X55 @ ( k2_tops_1 @ X56 @ X55 ) ) )
      | ~ ( l1_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('98',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('102',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('104',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['103','106'])).

thf('108',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('109',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('110',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('112',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['110','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('116',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      | ~ ( r1_tarski @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['114','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('120',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('123',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['121','124'])).

thf('126',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('130',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['125','130'])).

thf('132',plain,
    ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['118','131'])).

thf('133',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('134',plain,
    ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('137',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('140',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('141',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('142',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ X0 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['139','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('145',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ X0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('147',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('149',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('152',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('154',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('157',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['155','158'])).

thf('160',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['152','159'])).

thf('161',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('162',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('163',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['160','161','162'])).

thf('164',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['95','102','138','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('166',plain,(
    ! [X42: $i,X44: $i] :
      ( ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( r1_tarski @ X42 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('169',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('170',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X42: $i,X44: $i] :
      ( ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( r1_tarski @ X42 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('172',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) )
      | ( ( k4_subset_1 @ X33 @ X32 @ X34 )
        = ( k2_xboole_0 @ X32 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ X0 @ X1 )
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['167','174'])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('178',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['175','176','179'])).

thf('181',plain,
    ( ( ( k4_subset_1 @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['164','180'])).

thf('182',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['95','102','138','163'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('184',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['95','102','138','163'])).

thf('185',plain,
    ( ( ( k4_subset_1 @ sk_B @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['181','182','183','184'])).

thf('186',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('188',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ X0 @ X1 )
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('190',plain,
    ( ( ( k4_subset_1 @ sk_B @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','13'])).

thf('192',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('193',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X42: $i,X44: $i] :
      ( ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( r1_tarski @ X42 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('195',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('197',plain,(
    ! [X42: $i,X44: $i] :
      ( ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( r1_tarski @ X42 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('198',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) )
      | ( ( k4_subset_1 @ X33 @ X32 @ X34 )
        = ( k2_xboole_0 @ X32 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X1 )
        = ( k2_xboole_0 @ sk_B @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,
    ( ( ( k4_subset_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['195','200'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('203',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['168','169'])).

thf('204',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 )
      | ~ ( r1_tarski @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['125','130'])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['202','207'])).

thf('209',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('210',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('211',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['208','211'])).

thf('213',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('214',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X31 @ ( k3_subset_1 @ X31 @ X30 ) )
        = X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('215',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['212','215'])).

thf('217',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('218',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X31 @ ( k3_subset_1 @ X31 @ X30 ) )
        = X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('219',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('221',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['220','221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('224',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('225',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('227',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['222','225','226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['219','227'])).

thf('229',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['216','228'])).

thf('230',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['229','230'])).

thf('232',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('233',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['231','232'])).

thf('234',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['229','230'])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['233','234'])).

thf('236',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['201','235'])).

thf('237',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('238',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['236','237'])).

thf('239',plain,
    ( ( ( k4_subset_1 @ sk_B @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['190','238'])).

thf('240',plain,
    ( ( sk_B
      = ( k2_pre_topc @ sk_A @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['185','239'])).

thf('241',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('242',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( l1_pre_topc @ X49 )
      | ~ ( v2_pre_topc @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X49 @ X50 ) @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('243',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['243','244','245'])).

thf('247',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['240','246'])).

thf('248',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['63'])).

thf('249',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['247','248'])).

thf('250',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['55'])).

thf('251',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['64','249','250'])).

thf('252',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['62','251'])).

thf('253',plain,
    ( sk_B
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','252'])).

thf('254',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('255',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('256',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','253','254','255'])).

thf('257',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('258',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('259',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('260',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['258','259'])).

thf('261',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['257','260'])).

thf('262',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('263',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X2 ) ),
    inference('sup-',[status(thm)],['261','262'])).

thf('264',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('265',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['263','264'])).

thf('266',plain,
    ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['256','265'])).

thf('267',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('268',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('269',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('270',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['268','269'])).

thf('271',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('272',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['270','271'])).

thf('273',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('274',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X31 @ ( k3_subset_1 @ X31 @ X30 ) )
        = X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('275',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['273','274'])).

thf('276',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('277',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['275','276'])).

thf('278',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['272','277'])).

thf('279',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['267','278'])).

thf('280',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('281',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['279','280'])).

thf('282',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('283',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['156','157'])).

thf('284',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['275','276'])).

thf('285',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['283','284'])).

thf('286',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('287',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('288',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['285','286','287'])).

thf('289',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('290',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['288','289'])).

thf('291',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('292',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['222','225','226'])).

thf('293',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['291','292'])).

thf('294',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('295',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['293','294'])).

thf('296',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('297',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['295','296'])).

thf('298',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('299',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['297','298'])).

thf('300',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['291','292'])).

thf('301',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['299','300'])).

thf('302',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['290','301'])).

thf('303',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['282','302'])).

thf('304',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('305',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['303','304'])).

thf('306',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('307',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('308',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['305','306','307'])).

thf('309',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['281','308'])).

thf('310',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('311',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( ( k7_subset_1 @ X36 @ X35 @ X37 )
        = ( k4_xboole_0 @ X35 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('312',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['310','311'])).

thf('313',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['309','312'])).

thf('314',plain,
    ( ( k7_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['266','313'])).

thf('315',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['310','311'])).

thf('316',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('317',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['315','316'])).

thf('318',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','137'])).

thf('319',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['314','317','318'])).

thf('320',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['63'])).

thf('321',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('322',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('323',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['310','311'])).

thf('324',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('325',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X1 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['323','324'])).

thf('326',plain,
    ( ( k7_subset_1 @ sk_B @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['322','325'])).

thf('327',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['310','311'])).

thf('328',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['326','327'])).

thf('329',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['320','321','328'])).

thf('330',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['64','249'])).

thf('331',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['329','330'])).

thf('332',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['319','331'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.g6uZEiQUme
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:02:03 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 9.24/9.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.24/9.44  % Solved by: fo/fo7.sh
% 9.24/9.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.24/9.44  % done 17296 iterations in 8.992s
% 9.24/9.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.24/9.44  % SZS output start Refutation
% 9.24/9.44  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 9.24/9.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.24/9.44  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 9.24/9.44  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 9.24/9.44  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 9.24/9.44  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 9.24/9.44  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 9.24/9.44  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 9.24/9.44  thf(sk_B_type, type, sk_B: $i).
% 9.24/9.44  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 9.24/9.44  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 9.24/9.44  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 9.24/9.44  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 9.24/9.44  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 9.24/9.44  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 9.24/9.44  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 9.24/9.44  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 9.24/9.44  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 9.24/9.44  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 9.24/9.44  thf(sk_A_type, type, sk_A: $i).
% 9.24/9.44  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 9.24/9.44  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 9.24/9.44  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 9.24/9.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.24/9.44  thf(commutativity_k2_tarski, axiom,
% 9.24/9.44    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 9.24/9.44  thf('0', plain,
% 9.24/9.44      (![X21 : $i, X22 : $i]:
% 9.24/9.44         ((k2_tarski @ X22 @ X21) = (k2_tarski @ X21 @ X22))),
% 9.24/9.44      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 9.24/9.44  thf(l51_zfmisc_1, axiom,
% 9.24/9.44    (![A:$i,B:$i]:
% 9.24/9.44     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 9.24/9.44  thf('1', plain,
% 9.24/9.44      (![X23 : $i, X24 : $i]:
% 9.24/9.44         ((k3_tarski @ (k2_tarski @ X23 @ X24)) = (k2_xboole_0 @ X23 @ X24))),
% 9.24/9.44      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 9.24/9.44  thf('2', plain,
% 9.24/9.44      (![X0 : $i, X1 : $i]:
% 9.24/9.44         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 9.24/9.44      inference('sup+', [status(thm)], ['0', '1'])).
% 9.24/9.44  thf('3', plain,
% 9.24/9.44      (![X23 : $i, X24 : $i]:
% 9.24/9.44         ((k3_tarski @ (k2_tarski @ X23 @ X24)) = (k2_xboole_0 @ X23 @ X24))),
% 9.24/9.44      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 9.24/9.44  thf('4', plain,
% 9.24/9.44      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.24/9.44      inference('sup+', [status(thm)], ['2', '3'])).
% 9.24/9.44  thf(t36_xboole_1, axiom,
% 9.24/9.44    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 9.24/9.44  thf('5', plain,
% 9.24/9.44      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 9.24/9.44      inference('cnf', [status(esa)], [t36_xboole_1])).
% 9.24/9.44  thf(t44_xboole_1, axiom,
% 9.24/9.44    (![A:$i,B:$i,C:$i]:
% 9.24/9.44     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 9.24/9.44       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 9.24/9.44  thf('6', plain,
% 9.24/9.44      (![X14 : $i, X15 : $i, X16 : $i]:
% 9.24/9.44         ((r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 9.24/9.45          | ~ (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16))),
% 9.24/9.45      inference('cnf', [status(esa)], [t44_xboole_1])).
% 9.24/9.45  thf('7', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['5', '6'])).
% 9.24/9.45  thf(t77_tops_1, conjecture,
% 9.24/9.45    (![A:$i]:
% 9.24/9.45     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 9.24/9.45       ( ![B:$i]:
% 9.24/9.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.24/9.45           ( ( v4_pre_topc @ B @ A ) <=>
% 9.24/9.45             ( ( k2_tops_1 @ A @ B ) =
% 9.24/9.45               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 9.24/9.45  thf(zf_stmt_0, negated_conjecture,
% 9.24/9.45    (~( ![A:$i]:
% 9.24/9.45        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 9.24/9.45          ( ![B:$i]:
% 9.24/9.45            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.24/9.45              ( ( v4_pre_topc @ B @ A ) <=>
% 9.24/9.45                ( ( k2_tops_1 @ A @ B ) =
% 9.24/9.45                  ( k7_subset_1 @
% 9.24/9.45                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 9.24/9.45    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 9.24/9.45  thf('8', plain,
% 9.24/9.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.24/9.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.24/9.45  thf(t3_subset, axiom,
% 9.24/9.45    (![A:$i,B:$i]:
% 9.24/9.45     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 9.24/9.45  thf('9', plain,
% 9.24/9.45      (![X42 : $i, X43 : $i]:
% 9.24/9.45         ((r1_tarski @ X42 @ X43) | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43)))),
% 9.24/9.45      inference('cnf', [status(esa)], [t3_subset])).
% 9.24/9.45  thf('10', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 9.24/9.45      inference('sup-', [status(thm)], ['8', '9'])).
% 9.24/9.45  thf(t1_xboole_1, axiom,
% 9.24/9.45    (![A:$i,B:$i,C:$i]:
% 9.24/9.45     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 9.24/9.45       ( r1_tarski @ A @ C ) ))).
% 9.24/9.45  thf('11', plain,
% 9.24/9.45      (![X2 : $i, X3 : $i, X4 : $i]:
% 9.24/9.45         (~ (r1_tarski @ X2 @ X3)
% 9.24/9.45          | ~ (r1_tarski @ X3 @ X4)
% 9.24/9.45          | (r1_tarski @ X2 @ X4))),
% 9.24/9.45      inference('cnf', [status(esa)], [t1_xboole_1])).
% 9.24/9.45  thf('12', plain,
% 9.24/9.45      (![X0 : $i]:
% 9.24/9.45         ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['10', '11'])).
% 9.24/9.45  thf('13', plain,
% 9.24/9.45      (![X0 : $i]:
% 9.24/9.45         (r1_tarski @ sk_B @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))),
% 9.24/9.45      inference('sup-', [status(thm)], ['7', '12'])).
% 9.24/9.45  thf('14', plain,
% 9.24/9.45      (![X0 : $i]:
% 9.24/9.45         (r1_tarski @ sk_B @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))),
% 9.24/9.45      inference('sup+', [status(thm)], ['4', '13'])).
% 9.24/9.45  thf(t43_xboole_1, axiom,
% 9.24/9.45    (![A:$i,B:$i,C:$i]:
% 9.24/9.45     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 9.24/9.45       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 9.24/9.45  thf('15', plain,
% 9.24/9.45      (![X11 : $i, X12 : $i, X13 : $i]:
% 9.24/9.45         ((r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 9.24/9.45          | ~ (r1_tarski @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 9.24/9.45      inference('cnf', [status(esa)], [t43_xboole_1])).
% 9.24/9.45  thf('16', plain,
% 9.24/9.45      (![X0 : $i]:
% 9.24/9.45         (r1_tarski @ (k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)),
% 9.24/9.45      inference('sup-', [status(thm)], ['14', '15'])).
% 9.24/9.45  thf(t38_xboole_1, axiom,
% 9.24/9.45    (![A:$i,B:$i]:
% 9.24/9.45     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 9.24/9.45       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 9.24/9.45  thf('17', plain,
% 9.24/9.45      (![X8 : $i, X9 : $i]:
% 9.24/9.45         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 9.24/9.45      inference('cnf', [status(esa)], [t38_xboole_1])).
% 9.24/9.45  thf('18', plain,
% 9.24/9.45      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['16', '17'])).
% 9.24/9.45  thf(t48_xboole_1, axiom,
% 9.24/9.45    (![A:$i,B:$i]:
% 9.24/9.45     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 9.24/9.45  thf('19', plain,
% 9.24/9.45      (![X17 : $i, X18 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.24/9.45           = (k3_xboole_0 @ X17 @ X18))),
% 9.24/9.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.24/9.45  thf('20', plain,
% 9.24/9.45      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 9.24/9.45         = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 9.24/9.45      inference('sup+', [status(thm)], ['18', '19'])).
% 9.24/9.45  thf(t3_boole, axiom,
% 9.24/9.45    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 9.24/9.45  thf('21', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 9.24/9.45      inference('cnf', [status(esa)], [t3_boole])).
% 9.24/9.45  thf('22', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 9.24/9.45      inference('demod', [status(thm)], ['20', '21'])).
% 9.24/9.45  thf('23', plain,
% 9.24/9.45      (![X21 : $i, X22 : $i]:
% 9.24/9.45         ((k2_tarski @ X22 @ X21) = (k2_tarski @ X21 @ X22))),
% 9.24/9.45      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 9.24/9.45  thf(t12_setfam_1, axiom,
% 9.24/9.45    (![A:$i,B:$i]:
% 9.24/9.45     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 9.24/9.45  thf('24', plain,
% 9.24/9.45      (![X40 : $i, X41 : $i]:
% 9.24/9.45         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 9.24/9.45      inference('cnf', [status(esa)], [t12_setfam_1])).
% 9.24/9.45  thf('25', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('sup+', [status(thm)], ['23', '24'])).
% 9.24/9.45  thf('26', plain,
% 9.24/9.45      (![X40 : $i, X41 : $i]:
% 9.24/9.45         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 9.24/9.45      inference('cnf', [status(esa)], [t12_setfam_1])).
% 9.24/9.45  thf('27', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('sup+', [status(thm)], ['25', '26'])).
% 9.24/9.45  thf(t100_xboole_1, axiom,
% 9.24/9.45    (![A:$i,B:$i]:
% 9.24/9.45     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 9.24/9.45  thf('28', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X0 @ X1)
% 9.24/9.45           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 9.24/9.45      inference('cnf', [status(esa)], [t100_xboole_1])).
% 9.24/9.45  thf('29', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X0 @ X1)
% 9.24/9.45           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 9.24/9.45      inference('sup+', [status(thm)], ['27', '28'])).
% 9.24/9.45  thf('30', plain,
% 9.24/9.45      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 9.24/9.45         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 9.24/9.45      inference('sup+', [status(thm)], ['22', '29'])).
% 9.24/9.45  thf('31', plain,
% 9.24/9.45      (![X17 : $i, X18 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.24/9.45           = (k3_xboole_0 @ X17 @ X18))),
% 9.24/9.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.24/9.45  thf('32', plain,
% 9.24/9.45      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 9.24/9.45         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 9.24/9.45         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 9.24/9.45      inference('sup+', [status(thm)], ['30', '31'])).
% 9.24/9.45  thf('33', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('sup+', [status(thm)], ['25', '26'])).
% 9.24/9.45  thf('34', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 9.24/9.45      inference('demod', [status(thm)], ['20', '21'])).
% 9.24/9.45  thf('35', plain,
% 9.24/9.45      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 9.24/9.45         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 9.24/9.45      inference('demod', [status(thm)], ['32', '33', '34'])).
% 9.24/9.45  thf('36', plain,
% 9.24/9.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.24/9.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.24/9.45  thf(dt_k2_tops_1, axiom,
% 9.24/9.45    (![A:$i,B:$i]:
% 9.24/9.45     ( ( ( l1_pre_topc @ A ) & 
% 9.24/9.45         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 9.24/9.45       ( m1_subset_1 @
% 9.24/9.45         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 9.24/9.45  thf('37', plain,
% 9.24/9.45      (![X47 : $i, X48 : $i]:
% 9.24/9.45         (~ (l1_pre_topc @ X47)
% 9.24/9.45          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 9.24/9.45          | (m1_subset_1 @ (k2_tops_1 @ X47 @ X48) @ 
% 9.24/9.45             (k1_zfmisc_1 @ (u1_struct_0 @ X47))))),
% 9.24/9.45      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 9.24/9.45  thf('38', plain,
% 9.24/9.45      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 9.24/9.45         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 9.24/9.45        | ~ (l1_pre_topc @ sk_A))),
% 9.24/9.45      inference('sup-', [status(thm)], ['36', '37'])).
% 9.24/9.45  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 9.24/9.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.24/9.45  thf('40', plain,
% 9.24/9.45      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 9.24/9.45        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.24/9.45      inference('demod', [status(thm)], ['38', '39'])).
% 9.24/9.45  thf('41', plain,
% 9.24/9.45      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 9.24/9.45      inference('cnf', [status(esa)], [t36_xboole_1])).
% 9.24/9.45  thf('42', plain,
% 9.24/9.45      (![X42 : $i, X44 : $i]:
% 9.24/9.45         ((m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X44)) | ~ (r1_tarski @ X42 @ X44))),
% 9.24/9.45      inference('cnf', [status(esa)], [t3_subset])).
% 9.24/9.45  thf('43', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['41', '42'])).
% 9.24/9.45  thf(redefinition_k4_subset_1, axiom,
% 9.24/9.45    (![A:$i,B:$i,C:$i]:
% 9.24/9.45     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 9.24/9.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 9.24/9.45       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 9.24/9.45  thf('44', plain,
% 9.24/9.45      (![X32 : $i, X33 : $i, X34 : $i]:
% 9.24/9.45         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 9.24/9.45          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33))
% 9.24/9.45          | ((k4_subset_1 @ X33 @ X32 @ X34) = (k2_xboole_0 @ X32 @ X34)))),
% 9.24/9.45      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 9.24/9.45  thf('45', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.24/9.45         (((k4_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 9.24/9.45            = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))
% 9.24/9.45          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0)))),
% 9.24/9.45      inference('sup-', [status(thm)], ['43', '44'])).
% 9.24/9.45  thf('46', plain,
% 9.24/9.45      (![X0 : $i]:
% 9.24/9.45         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.24/9.45           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 9.24/9.45           (k2_tops_1 @ sk_A @ sk_B))
% 9.24/9.45           = (k2_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 9.24/9.45              (k2_tops_1 @ sk_A @ sk_B)))),
% 9.24/9.45      inference('sup-', [status(thm)], ['40', '45'])).
% 9.24/9.45  thf('47', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('sup+', [status(thm)], ['2', '3'])).
% 9.24/9.45  thf('48', plain,
% 9.24/9.45      (![X0 : $i]:
% 9.24/9.45         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 9.24/9.45           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 9.24/9.45           (k2_tops_1 @ sk_A @ sk_B))
% 9.24/9.45           = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 9.24/9.45              (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 9.24/9.45      inference('demod', [status(thm)], ['46', '47'])).
% 9.24/9.45  thf('49', plain,
% 9.24/9.45      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 9.24/9.45         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 9.24/9.45            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 9.24/9.45             (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 9.24/9.45      inference('sup+', [status(thm)], ['35', '48'])).
% 9.24/9.45  thf('50', plain,
% 9.24/9.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.24/9.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.24/9.45  thf(t65_tops_1, axiom,
% 9.24/9.45    (![A:$i]:
% 9.24/9.45     ( ( l1_pre_topc @ A ) =>
% 9.24/9.45       ( ![B:$i]:
% 9.24/9.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.24/9.45           ( ( k2_pre_topc @ A @ B ) =
% 9.24/9.45             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 9.24/9.45  thf('51', plain,
% 9.24/9.45      (![X53 : $i, X54 : $i]:
% 9.24/9.45         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 9.24/9.45          | ((k2_pre_topc @ X54 @ X53)
% 9.24/9.45              = (k4_subset_1 @ (u1_struct_0 @ X54) @ X53 @ 
% 9.24/9.45                 (k2_tops_1 @ X54 @ X53)))
% 9.24/9.45          | ~ (l1_pre_topc @ X54))),
% 9.24/9.45      inference('cnf', [status(esa)], [t65_tops_1])).
% 9.24/9.45  thf('52', plain,
% 9.24/9.45      ((~ (l1_pre_topc @ sk_A)
% 9.24/9.45        | ((k2_pre_topc @ sk_A @ sk_B)
% 9.24/9.45            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45               (k2_tops_1 @ sk_A @ sk_B))))),
% 9.24/9.45      inference('sup-', [status(thm)], ['50', '51'])).
% 9.24/9.45  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 9.24/9.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.24/9.45  thf('54', plain,
% 9.24/9.45      (((k2_pre_topc @ sk_A @ sk_B)
% 9.24/9.45         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45            (k2_tops_1 @ sk_A @ sk_B)))),
% 9.24/9.45      inference('demod', [status(thm)], ['52', '53'])).
% 9.24/9.45  thf('55', plain,
% 9.24/9.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45             (k1_tops_1 @ sk_A @ sk_B)))
% 9.24/9.45        | (v4_pre_topc @ sk_B @ sk_A))),
% 9.24/9.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.24/9.45  thf('56', plain,
% 9.24/9.45      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 9.24/9.45      inference('split', [status(esa)], ['55'])).
% 9.24/9.45  thf('57', plain,
% 9.24/9.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.24/9.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.24/9.45  thf(t52_pre_topc, axiom,
% 9.24/9.45    (![A:$i]:
% 9.24/9.45     ( ( l1_pre_topc @ A ) =>
% 9.24/9.45       ( ![B:$i]:
% 9.24/9.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.24/9.45           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 9.24/9.45             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 9.24/9.45               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 9.24/9.45  thf('58', plain,
% 9.24/9.45      (![X45 : $i, X46 : $i]:
% 9.24/9.45         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 9.24/9.45          | ~ (v4_pre_topc @ X45 @ X46)
% 9.24/9.45          | ((k2_pre_topc @ X46 @ X45) = (X45))
% 9.24/9.45          | ~ (l1_pre_topc @ X46))),
% 9.24/9.45      inference('cnf', [status(esa)], [t52_pre_topc])).
% 9.24/9.45  thf('59', plain,
% 9.24/9.45      ((~ (l1_pre_topc @ sk_A)
% 9.24/9.45        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 9.24/9.45        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 9.24/9.45      inference('sup-', [status(thm)], ['57', '58'])).
% 9.24/9.45  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 9.24/9.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.24/9.45  thf('61', plain,
% 9.24/9.45      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 9.24/9.45      inference('demod', [status(thm)], ['59', '60'])).
% 9.24/9.45  thf('62', plain,
% 9.24/9.45      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 9.24/9.45         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 9.24/9.45      inference('sup-', [status(thm)], ['56', '61'])).
% 9.24/9.45  thf('63', plain,
% 9.24/9.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45              (k1_tops_1 @ sk_A @ sk_B)))
% 9.24/9.45        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 9.24/9.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.24/9.45  thf('64', plain,
% 9.24/9.45      (~
% 9.24/9.45       (((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 9.24/9.45       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 9.24/9.45      inference('split', [status(esa)], ['63'])).
% 9.24/9.45  thf('65', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['41', '42'])).
% 9.24/9.45  thf(t25_subset_1, axiom,
% 9.24/9.45    (![A:$i,B:$i]:
% 9.24/9.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.24/9.45       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 9.24/9.45         ( k2_subset_1 @ A ) ) ))).
% 9.24/9.45  thf('66', plain,
% 9.24/9.45      (![X38 : $i, X39 : $i]:
% 9.24/9.45         (((k4_subset_1 @ X38 @ X39 @ (k3_subset_1 @ X38 @ X39))
% 9.24/9.45            = (k2_subset_1 @ X38))
% 9.24/9.45          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 9.24/9.45      inference('cnf', [status(esa)], [t25_subset_1])).
% 9.24/9.45  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 9.24/9.45  thf('67', plain, (![X25 : $i]: ((k2_subset_1 @ X25) = (X25))),
% 9.24/9.45      inference('cnf', [status(esa)], [d4_subset_1])).
% 9.24/9.45  thf('68', plain,
% 9.24/9.45      (![X38 : $i, X39 : $i]:
% 9.24/9.45         (((k4_subset_1 @ X38 @ X39 @ (k3_subset_1 @ X38 @ X39)) = (X38))
% 9.24/9.45          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 9.24/9.45      inference('demod', [status(thm)], ['66', '67'])).
% 9.24/9.45  thf('69', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k4_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 9.24/9.45           (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))) = (X0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['65', '68'])).
% 9.24/9.45  thf('70', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['41', '42'])).
% 9.24/9.45  thf(d5_subset_1, axiom,
% 9.24/9.45    (![A:$i,B:$i]:
% 9.24/9.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.24/9.45       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 9.24/9.45  thf('71', plain,
% 9.24/9.45      (![X26 : $i, X27 : $i]:
% 9.24/9.45         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 9.24/9.45          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 9.24/9.45      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.24/9.45  thf('72', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 9.24/9.45           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 9.24/9.45      inference('sup-', [status(thm)], ['70', '71'])).
% 9.24/9.45  thf('73', plain,
% 9.24/9.45      (![X17 : $i, X18 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.24/9.45           = (k3_xboole_0 @ X17 @ X18))),
% 9.24/9.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.24/9.45  thf('74', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 9.24/9.45           = (k3_xboole_0 @ X1 @ X0))),
% 9.24/9.45      inference('sup+', [status(thm)], ['72', '73'])).
% 9.24/9.45  thf('75', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k4_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1))
% 9.24/9.45           = (X0))),
% 9.24/9.45      inference('demod', [status(thm)], ['69', '74'])).
% 9.24/9.45  thf('76', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('sup+', [status(thm)], ['25', '26'])).
% 9.24/9.45  thf('77', plain,
% 9.24/9.45      (![X17 : $i, X18 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.24/9.45           = (k3_xboole_0 @ X17 @ X18))),
% 9.24/9.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.24/9.45  thf('78', plain,
% 9.24/9.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.24/9.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.24/9.45  thf(redefinition_k7_subset_1, axiom,
% 9.24/9.45    (![A:$i,B:$i,C:$i]:
% 9.24/9.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.24/9.45       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 9.24/9.45  thf('79', plain,
% 9.24/9.45      (![X35 : $i, X36 : $i, X37 : $i]:
% 9.24/9.45         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 9.24/9.45          | ((k7_subset_1 @ X36 @ X35 @ X37) = (k4_xboole_0 @ X35 @ X37)))),
% 9.24/9.45      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 9.24/9.45  thf('80', plain,
% 9.24/9.45      (![X0 : $i]:
% 9.24/9.45         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 9.24/9.45           = (k4_xboole_0 @ sk_B @ X0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['78', '79'])).
% 9.24/9.45  thf('81', plain,
% 9.24/9.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45             (k1_tops_1 @ sk_A @ sk_B))))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('split', [status(esa)], ['55'])).
% 9.24/9.45  thf('82', plain,
% 9.24/9.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('sup+', [status(thm)], ['80', '81'])).
% 9.24/9.45  thf('83', plain,
% 9.24/9.45      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 9.24/9.45      inference('cnf', [status(esa)], [t36_xboole_1])).
% 9.24/9.45  thf('84', plain,
% 9.24/9.45      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('sup+', [status(thm)], ['82', '83'])).
% 9.24/9.45  thf('85', plain,
% 9.24/9.45      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 9.24/9.45      inference('cnf', [status(esa)], [t36_xboole_1])).
% 9.24/9.45  thf('86', plain,
% 9.24/9.45      (![X2 : $i, X3 : $i, X4 : $i]:
% 9.24/9.45         (~ (r1_tarski @ X2 @ X3)
% 9.24/9.45          | ~ (r1_tarski @ X3 @ X4)
% 9.24/9.45          | (r1_tarski @ X2 @ X4))),
% 9.24/9.45      inference('cnf', [status(esa)], [t1_xboole_1])).
% 9.24/9.45  thf('87', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.24/9.45         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 9.24/9.45      inference('sup-', [status(thm)], ['85', '86'])).
% 9.24/9.45  thf('88', plain,
% 9.24/9.45      ((![X0 : $i]:
% 9.24/9.45          (r1_tarski @ (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0) @ sk_B))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('sup-', [status(thm)], ['84', '87'])).
% 9.24/9.45  thf('89', plain,
% 9.24/9.45      (![X42 : $i, X44 : $i]:
% 9.24/9.45         ((m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X44)) | ~ (r1_tarski @ X42 @ X44))),
% 9.24/9.45      inference('cnf', [status(esa)], [t3_subset])).
% 9.24/9.45  thf('90', plain,
% 9.24/9.45      ((![X0 : $i]:
% 9.24/9.45          (m1_subset_1 @ (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0) @ 
% 9.24/9.45           (k1_zfmisc_1 @ sk_B)))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('sup-', [status(thm)], ['88', '89'])).
% 9.24/9.45  thf('91', plain,
% 9.24/9.45      ((![X0 : $i]:
% 9.24/9.45          (m1_subset_1 @ (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0) @ 
% 9.24/9.45           (k1_zfmisc_1 @ sk_B)))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('sup+', [status(thm)], ['77', '90'])).
% 9.24/9.45  thf('92', plain,
% 9.24/9.45      ((![X0 : $i]:
% 9.24/9.45          (m1_subset_1 @ (k3_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 9.24/9.45           (k1_zfmisc_1 @ sk_B)))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('sup+', [status(thm)], ['76', '91'])).
% 9.24/9.45  thf('93', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.24/9.45         (((k4_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 9.24/9.45            = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))
% 9.24/9.45          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0)))),
% 9.24/9.45      inference('sup-', [status(thm)], ['43', '44'])).
% 9.24/9.45  thf('94', plain,
% 9.24/9.45      ((![X0 : $i, X1 : $i]:
% 9.24/9.45          ((k4_subset_1 @ sk_B @ (k4_xboole_0 @ sk_B @ X1) @ 
% 9.24/9.45            (k3_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)))
% 9.24/9.45            = (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ X1) @ 
% 9.24/9.45               (k3_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)))))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('sup-', [status(thm)], ['92', '93'])).
% 9.24/9.45  thf('95', plain,
% 9.24/9.45      ((((sk_B)
% 9.24/9.45          = (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 9.24/9.45             (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('sup+', [status(thm)], ['75', '94'])).
% 9.24/9.45  thf('96', plain,
% 9.24/9.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.24/9.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.24/9.45  thf(t74_tops_1, axiom,
% 9.24/9.45    (![A:$i]:
% 9.24/9.45     ( ( l1_pre_topc @ A ) =>
% 9.24/9.45       ( ![B:$i]:
% 9.24/9.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.24/9.45           ( ( k1_tops_1 @ A @ B ) =
% 9.24/9.45             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 9.24/9.45  thf('97', plain,
% 9.24/9.45      (![X55 : $i, X56 : $i]:
% 9.24/9.45         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 9.24/9.45          | ((k1_tops_1 @ X56 @ X55)
% 9.24/9.45              = (k7_subset_1 @ (u1_struct_0 @ X56) @ X55 @ 
% 9.24/9.45                 (k2_tops_1 @ X56 @ X55)))
% 9.24/9.45          | ~ (l1_pre_topc @ X56))),
% 9.24/9.45      inference('cnf', [status(esa)], [t74_tops_1])).
% 9.24/9.45  thf('98', plain,
% 9.24/9.45      ((~ (l1_pre_topc @ sk_A)
% 9.24/9.45        | ((k1_tops_1 @ sk_A @ sk_B)
% 9.24/9.45            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45               (k2_tops_1 @ sk_A @ sk_B))))),
% 9.24/9.45      inference('sup-', [status(thm)], ['96', '97'])).
% 9.24/9.45  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 9.24/9.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.24/9.45  thf('100', plain,
% 9.24/9.45      (((k1_tops_1 @ sk_A @ sk_B)
% 9.24/9.45         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45            (k2_tops_1 @ sk_A @ sk_B)))),
% 9.24/9.45      inference('demod', [status(thm)], ['98', '99'])).
% 9.24/9.45  thf('101', plain,
% 9.24/9.45      (![X0 : $i]:
% 9.24/9.45         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 9.24/9.45           = (k4_xboole_0 @ sk_B @ X0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['78', '79'])).
% 9.24/9.45  thf('102', plain,
% 9.24/9.45      (((k1_tops_1 @ sk_A @ sk_B)
% 9.24/9.45         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 9.24/9.45      inference('demod', [status(thm)], ['100', '101'])).
% 9.24/9.45  thf('103', plain,
% 9.24/9.45      (((k1_tops_1 @ sk_A @ sk_B)
% 9.24/9.45         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 9.24/9.45      inference('demod', [status(thm)], ['100', '101'])).
% 9.24/9.45  thf('104', plain,
% 9.24/9.45      (![X17 : $i, X18 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.24/9.45           = (k3_xboole_0 @ X17 @ X18))),
% 9.24/9.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.24/9.45  thf('105', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X0 @ X1)
% 9.24/9.45           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 9.24/9.45      inference('cnf', [status(esa)], [t100_xboole_1])).
% 9.24/9.45  thf('106', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k3_xboole_0 @ X1 @ X0)
% 9.24/9.45           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 9.24/9.45      inference('sup+', [status(thm)], ['104', '105'])).
% 9.24/9.45  thf('107', plain,
% 9.24/9.45      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 9.24/9.45         = (k5_xboole_0 @ sk_B @ 
% 9.24/9.45            (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))),
% 9.24/9.45      inference('sup+', [status(thm)], ['103', '106'])).
% 9.24/9.45  thf('108', plain,
% 9.24/9.45      (((k1_tops_1 @ sk_A @ sk_B)
% 9.24/9.45         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 9.24/9.45      inference('demod', [status(thm)], ['100', '101'])).
% 9.24/9.45  thf('109', plain,
% 9.24/9.45      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 9.24/9.45      inference('cnf', [status(esa)], [t36_xboole_1])).
% 9.24/9.45  thf('110', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 9.24/9.45      inference('sup+', [status(thm)], ['108', '109'])).
% 9.24/9.45  thf('111', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 9.24/9.45      inference('cnf', [status(esa)], [t3_boole])).
% 9.24/9.45  thf('112', plain,
% 9.24/9.45      (![X14 : $i, X15 : $i, X16 : $i]:
% 9.24/9.45         ((r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 9.24/9.45          | ~ (r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16))),
% 9.24/9.45      inference('cnf', [status(esa)], [t44_xboole_1])).
% 9.24/9.45  thf('113', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         (~ (r1_tarski @ X0 @ X1)
% 9.24/9.45          | (r1_tarski @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1)))),
% 9.24/9.45      inference('sup-', [status(thm)], ['111', '112'])).
% 9.24/9.45  thf('114', plain,
% 9.24/9.45      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 9.24/9.45        (k2_xboole_0 @ k1_xboole_0 @ sk_B))),
% 9.24/9.45      inference('sup-', [status(thm)], ['110', '113'])).
% 9.24/9.45  thf('115', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('sup+', [status(thm)], ['2', '3'])).
% 9.24/9.45  thf('116', plain,
% 9.24/9.45      (![X11 : $i, X12 : $i, X13 : $i]:
% 9.24/9.45         ((r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 9.24/9.45          | ~ (r1_tarski @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 9.24/9.45      inference('cnf', [status(esa)], [t43_xboole_1])).
% 9.24/9.45  thf('117', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.24/9.45         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 9.24/9.45          | (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 9.24/9.45      inference('sup-', [status(thm)], ['115', '116'])).
% 9.24/9.45  thf('118', plain,
% 9.24/9.45      ((r1_tarski @ (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B) @ 
% 9.24/9.45        k1_xboole_0)),
% 9.24/9.45      inference('sup-', [status(thm)], ['114', '117'])).
% 9.24/9.45  thf('119', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('sup+', [status(thm)], ['25', '26'])).
% 9.24/9.45  thf(t2_boole, axiom,
% 9.24/9.45    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 9.24/9.45  thf('120', plain,
% 9.24/9.45      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 9.24/9.45      inference('cnf', [status(esa)], [t2_boole])).
% 9.24/9.45  thf('121', plain,
% 9.24/9.45      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 9.24/9.45      inference('sup+', [status(thm)], ['119', '120'])).
% 9.24/9.45  thf('122', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X0 @ X1)
% 9.24/9.45           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 9.24/9.45      inference('cnf', [status(esa)], [t100_xboole_1])).
% 9.24/9.45  thf('123', plain,
% 9.24/9.45      (![X8 : $i, X9 : $i]:
% 9.24/9.45         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 9.24/9.45      inference('cnf', [status(esa)], [t38_xboole_1])).
% 9.24/9.45  thf('124', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         (~ (r1_tarski @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 9.24/9.45          | ((X0) = (k1_xboole_0)))),
% 9.24/9.45      inference('sup-', [status(thm)], ['122', '123'])).
% 9.24/9.45  thf('125', plain,
% 9.24/9.45      (![X0 : $i]:
% 9.24/9.45         (~ (r1_tarski @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 9.24/9.45          | ((X0) = (k1_xboole_0)))),
% 9.24/9.45      inference('sup-', [status(thm)], ['121', '124'])).
% 9.24/9.45  thf('126', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 9.24/9.45      inference('cnf', [status(esa)], [t3_boole])).
% 9.24/9.45  thf('127', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X0 @ X1)
% 9.24/9.45           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 9.24/9.45      inference('cnf', [status(esa)], [t100_xboole_1])).
% 9.24/9.45  thf('128', plain,
% 9.24/9.45      (![X0 : $i]:
% 9.24/9.45         ((X0) = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 9.24/9.45      inference('sup+', [status(thm)], ['126', '127'])).
% 9.24/9.45  thf('129', plain,
% 9.24/9.45      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 9.24/9.45      inference('cnf', [status(esa)], [t2_boole])).
% 9.24/9.45  thf('130', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 9.24/9.45      inference('demod', [status(thm)], ['128', '129'])).
% 9.24/9.45  thf('131', plain,
% 9.24/9.45      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 9.24/9.45      inference('demod', [status(thm)], ['125', '130'])).
% 9.24/9.45  thf('132', plain,
% 9.24/9.45      (((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['118', '131'])).
% 9.24/9.45  thf('133', plain,
% 9.24/9.45      (![X17 : $i, X18 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.24/9.45           = (k3_xboole_0 @ X17 @ X18))),
% 9.24/9.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.24/9.45  thf('134', plain,
% 9.24/9.45      (((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 9.24/9.45         = (k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 9.24/9.45      inference('sup+', [status(thm)], ['132', '133'])).
% 9.24/9.45  thf('135', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 9.24/9.45      inference('cnf', [status(esa)], [t3_boole])).
% 9.24/9.45  thf('136', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('sup+', [status(thm)], ['25', '26'])).
% 9.24/9.45  thf('137', plain,
% 9.24/9.45      (((k1_tops_1 @ sk_A @ sk_B)
% 9.24/9.45         = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 9.24/9.45      inference('demod', [status(thm)], ['134', '135', '136'])).
% 9.24/9.45  thf('138', plain,
% 9.24/9.45      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 9.24/9.45         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 9.24/9.45      inference('demod', [status(thm)], ['107', '137'])).
% 9.24/9.45  thf('139', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['5', '6'])).
% 9.24/9.45  thf('140', plain,
% 9.24/9.45      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('sup+', [status(thm)], ['82', '83'])).
% 9.24/9.45  thf('141', plain,
% 9.24/9.45      (![X2 : $i, X3 : $i, X4 : $i]:
% 9.24/9.45         (~ (r1_tarski @ X2 @ X3)
% 9.24/9.45          | ~ (r1_tarski @ X3 @ X4)
% 9.24/9.45          | (r1_tarski @ X2 @ X4))),
% 9.24/9.45      inference('cnf', [status(esa)], [t1_xboole_1])).
% 9.24/9.45  thf('142', plain,
% 9.24/9.45      ((![X0 : $i]:
% 9.24/9.45          ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 9.24/9.45           | ~ (r1_tarski @ sk_B @ X0)))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('sup-', [status(thm)], ['140', '141'])).
% 9.24/9.45  thf('143', plain,
% 9.24/9.45      ((![X0 : $i]:
% 9.24/9.45          (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_xboole_0 @ X0 @ sk_B)))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('sup-', [status(thm)], ['139', '142'])).
% 9.24/9.45  thf('144', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.24/9.45         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 9.24/9.45          | (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 9.24/9.45      inference('sup-', [status(thm)], ['115', '116'])).
% 9.24/9.45  thf('145', plain,
% 9.24/9.45      ((![X0 : $i]:
% 9.24/9.45          (r1_tarski @ (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ X0))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('sup-', [status(thm)], ['143', '144'])).
% 9.24/9.45  thf('146', plain,
% 9.24/9.45      (![X8 : $i, X9 : $i]:
% 9.24/9.45         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 9.24/9.45      inference('cnf', [status(esa)], [t38_xboole_1])).
% 9.24/9.45  thf('147', plain,
% 9.24/9.45      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('sup-', [status(thm)], ['145', '146'])).
% 9.24/9.45  thf('148', plain,
% 9.24/9.45      (![X17 : $i, X18 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.24/9.45           = (k3_xboole_0 @ X17 @ X18))),
% 9.24/9.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.24/9.45  thf('149', plain,
% 9.24/9.45      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 9.24/9.45          = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('sup+', [status(thm)], ['147', '148'])).
% 9.24/9.45  thf('150', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 9.24/9.45      inference('cnf', [status(esa)], [t3_boole])).
% 9.24/9.45  thf('151', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('sup+', [status(thm)], ['25', '26'])).
% 9.24/9.45  thf('152', plain,
% 9.24/9.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('demod', [status(thm)], ['149', '150', '151'])).
% 9.24/9.45  thf('153', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X0 @ X1)
% 9.24/9.45           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 9.24/9.45      inference('cnf', [status(esa)], [t100_xboole_1])).
% 9.24/9.45  thf('154', plain,
% 9.24/9.45      (![X17 : $i, X18 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.24/9.45           = (k3_xboole_0 @ X17 @ X18))),
% 9.24/9.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.24/9.45  thf('155', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 9.24/9.45           = (k3_xboole_0 @ X1 @ X0))),
% 9.24/9.45      inference('sup+', [status(thm)], ['153', '154'])).
% 9.24/9.45  thf('156', plain,
% 9.24/9.45      (![X17 : $i, X18 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.24/9.45           = (k3_xboole_0 @ X17 @ X18))),
% 9.24/9.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.24/9.45  thf('157', plain,
% 9.24/9.45      (![X17 : $i, X18 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.24/9.45           = (k3_xboole_0 @ X17 @ X18))),
% 9.24/9.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.24/9.45  thf('158', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 9.24/9.45           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 9.24/9.45      inference('sup+', [status(thm)], ['156', '157'])).
% 9.24/9.45  thf('159', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 9.24/9.45           = (k3_xboole_0 @ X1 @ X0))),
% 9.24/9.45      inference('demod', [status(thm)], ['155', '158'])).
% 9.24/9.45  thf('160', plain,
% 9.24/9.45      ((((k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 9.24/9.45          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('sup+', [status(thm)], ['152', '159'])).
% 9.24/9.45  thf('161', plain,
% 9.24/9.45      (((k1_tops_1 @ sk_A @ sk_B)
% 9.24/9.45         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 9.24/9.45      inference('demod', [status(thm)], ['100', '101'])).
% 9.24/9.45  thf('162', plain,
% 9.24/9.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('demod', [status(thm)], ['149', '150', '151'])).
% 9.24/9.45  thf('163', plain,
% 9.24/9.45      ((((k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 9.24/9.45          = (k2_tops_1 @ sk_A @ sk_B)))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('demod', [status(thm)], ['160', '161', '162'])).
% 9.24/9.45  thf('164', plain,
% 9.24/9.45      ((((sk_B)
% 9.24/9.45          = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 9.24/9.45             (k2_tops_1 @ sk_A @ sk_B))))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('demod', [status(thm)], ['95', '102', '138', '163'])).
% 9.24/9.45  thf('165', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['5', '6'])).
% 9.24/9.45  thf('166', plain,
% 9.24/9.45      (![X42 : $i, X44 : $i]:
% 9.24/9.45         ((m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X44)) | ~ (r1_tarski @ X42 @ X44))),
% 9.24/9.45      inference('cnf', [status(esa)], [t3_subset])).
% 9.24/9.45  thf('167', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 9.24/9.45      inference('sup-', [status(thm)], ['165', '166'])).
% 9.24/9.45  thf('168', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 9.24/9.45      inference('cnf', [status(esa)], [t3_boole])).
% 9.24/9.45  thf('169', plain,
% 9.24/9.45      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 9.24/9.45      inference('cnf', [status(esa)], [t36_xboole_1])).
% 9.24/9.45  thf('170', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 9.24/9.45      inference('sup+', [status(thm)], ['168', '169'])).
% 9.24/9.45  thf('171', plain,
% 9.24/9.45      (![X42 : $i, X44 : $i]:
% 9.24/9.45         ((m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X44)) | ~ (r1_tarski @ X42 @ X44))),
% 9.24/9.45      inference('cnf', [status(esa)], [t3_subset])).
% 9.24/9.45  thf('172', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['170', '171'])).
% 9.24/9.45  thf('173', plain,
% 9.24/9.45      (![X32 : $i, X33 : $i, X34 : $i]:
% 9.24/9.45         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 9.24/9.45          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33))
% 9.24/9.45          | ((k4_subset_1 @ X33 @ X32 @ X34) = (k2_xboole_0 @ X32 @ X34)))),
% 9.24/9.45      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 9.24/9.45  thf('174', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         (((k4_subset_1 @ X0 @ X0 @ X1) = (k2_xboole_0 @ X0 @ X1))
% 9.24/9.45          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 9.24/9.45      inference('sup-', [status(thm)], ['172', '173'])).
% 9.24/9.45  thf('175', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k4_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 9.24/9.45           = (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['167', '174'])).
% 9.24/9.45  thf('176', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('sup+', [status(thm)], ['2', '3'])).
% 9.24/9.45  thf('177', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('sup+', [status(thm)], ['2', '3'])).
% 9.24/9.45  thf(t6_xboole_1, axiom,
% 9.24/9.45    (![A:$i,B:$i]:
% 9.24/9.45     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 9.24/9.45  thf('178', plain,
% 9.24/9.45      (![X19 : $i, X20 : $i]:
% 9.24/9.45         ((k2_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20))
% 9.24/9.45           = (k2_xboole_0 @ X19 @ X20))),
% 9.24/9.45      inference('cnf', [status(esa)], [t6_xboole_1])).
% 9.24/9.45  thf('179', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 9.24/9.45           = (k2_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('sup+', [status(thm)], ['177', '178'])).
% 9.24/9.45  thf('180', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k4_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 9.24/9.45           = (k2_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('demod', [status(thm)], ['175', '176', '179'])).
% 9.24/9.45  thf('181', plain,
% 9.24/9.45      ((((k4_subset_1 @ 
% 9.24/9.45          (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 9.24/9.45          sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 9.24/9.45          = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 9.24/9.45             (k1_tops_1 @ sk_A @ sk_B))))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('sup+', [status(thm)], ['164', '180'])).
% 9.24/9.45  thf('182', plain,
% 9.24/9.45      ((((sk_B)
% 9.24/9.45          = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 9.24/9.45             (k2_tops_1 @ sk_A @ sk_B))))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('demod', [status(thm)], ['95', '102', '138', '163'])).
% 9.24/9.45  thf('183', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('sup+', [status(thm)], ['2', '3'])).
% 9.24/9.45  thf('184', plain,
% 9.24/9.45      ((((sk_B)
% 9.24/9.45          = (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 9.24/9.45             (k2_tops_1 @ sk_A @ sk_B))))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('demod', [status(thm)], ['95', '102', '138', '163'])).
% 9.24/9.45  thf('185', plain,
% 9.24/9.45      ((((k4_subset_1 @ sk_B @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('demod', [status(thm)], ['181', '182', '183', '184'])).
% 9.24/9.45  thf('186', plain,
% 9.24/9.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('sup+', [status(thm)], ['80', '81'])).
% 9.24/9.45  thf('187', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['41', '42'])).
% 9.24/9.45  thf('188', plain,
% 9.24/9.45      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B)))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('sup+', [status(thm)], ['186', '187'])).
% 9.24/9.45  thf('189', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         (((k4_subset_1 @ X0 @ X0 @ X1) = (k2_xboole_0 @ X0 @ X1))
% 9.24/9.45          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 9.24/9.45      inference('sup-', [status(thm)], ['172', '173'])).
% 9.24/9.45  thf('190', plain,
% 9.24/9.45      ((((k4_subset_1 @ sk_B @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 9.24/9.45          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('sup-', [status(thm)], ['188', '189'])).
% 9.24/9.45  thf('191', plain,
% 9.24/9.45      (![X0 : $i]:
% 9.24/9.45         (r1_tarski @ sk_B @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))),
% 9.24/9.45      inference('sup+', [status(thm)], ['4', '13'])).
% 9.24/9.45  thf('192', plain,
% 9.24/9.45      ((![X0 : $i]:
% 9.24/9.45          ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 9.24/9.45           | ~ (r1_tarski @ sk_B @ X0)))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('sup-', [status(thm)], ['140', '141'])).
% 9.24/9.45  thf('193', plain,
% 9.24/9.45      ((![X0 : $i]:
% 9.24/9.45          (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 9.24/9.45           (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('sup-', [status(thm)], ['191', '192'])).
% 9.24/9.45  thf('194', plain,
% 9.24/9.45      (![X42 : $i, X44 : $i]:
% 9.24/9.45         ((m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X44)) | ~ (r1_tarski @ X42 @ X44))),
% 9.24/9.45      inference('cnf', [status(esa)], [t3_subset])).
% 9.24/9.45  thf('195', plain,
% 9.24/9.45      ((![X0 : $i]:
% 9.24/9.45          (m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 9.24/9.45           (k1_zfmisc_1 @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('sup-', [status(thm)], ['193', '194'])).
% 9.24/9.45  thf('196', plain,
% 9.24/9.45      (![X0 : $i]:
% 9.24/9.45         (r1_tarski @ sk_B @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))),
% 9.24/9.45      inference('sup-', [status(thm)], ['7', '12'])).
% 9.24/9.45  thf('197', plain,
% 9.24/9.45      (![X42 : $i, X44 : $i]:
% 9.24/9.45         ((m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X44)) | ~ (r1_tarski @ X42 @ X44))),
% 9.24/9.45      inference('cnf', [status(esa)], [t3_subset])).
% 9.24/9.45  thf('198', plain,
% 9.24/9.45      (![X0 : $i]:
% 9.24/9.45         (m1_subset_1 @ sk_B @ 
% 9.24/9.45          (k1_zfmisc_1 @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A))))),
% 9.24/9.45      inference('sup-', [status(thm)], ['196', '197'])).
% 9.24/9.45  thf('199', plain,
% 9.24/9.45      (![X32 : $i, X33 : $i, X34 : $i]:
% 9.24/9.45         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 9.24/9.45          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33))
% 9.24/9.45          | ((k4_subset_1 @ X33 @ X32 @ X34) = (k2_xboole_0 @ X32 @ X34)))),
% 9.24/9.45      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 9.24/9.45  thf('200', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         (((k4_subset_1 @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)) @ sk_B @ X1)
% 9.24/9.45            = (k2_xboole_0 @ sk_B @ X1))
% 9.24/9.45          | ~ (m1_subset_1 @ X1 @ 
% 9.24/9.45               (k1_zfmisc_1 @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))))),
% 9.24/9.45      inference('sup-', [status(thm)], ['198', '199'])).
% 9.24/9.45  thf('201', plain,
% 9.24/9.45      ((((k4_subset_1 @ 
% 9.24/9.45          (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ sk_B @ 
% 9.24/9.45          (k2_tops_1 @ sk_A @ sk_B))
% 9.24/9.45          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('sup-', [status(thm)], ['195', '200'])).
% 9.24/9.45  thf('202', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('sup+', [status(thm)], ['2', '3'])).
% 9.24/9.45  thf('203', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 9.24/9.45      inference('sup+', [status(thm)], ['168', '169'])).
% 9.24/9.45  thf('204', plain,
% 9.24/9.45      (![X11 : $i, X12 : $i, X13 : $i]:
% 9.24/9.45         ((r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X13)
% 9.24/9.45          | ~ (r1_tarski @ X11 @ (k2_xboole_0 @ X12 @ X13)))),
% 9.24/9.45      inference('cnf', [status(esa)], [t43_xboole_1])).
% 9.24/9.45  thf('205', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 9.24/9.45      inference('sup-', [status(thm)], ['203', '204'])).
% 9.24/9.45  thf('206', plain,
% 9.24/9.45      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 9.24/9.45      inference('demod', [status(thm)], ['125', '130'])).
% 9.24/9.45  thf('207', plain,
% 9.24/9.45      (![X0 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0) = (k1_xboole_0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['205', '206'])).
% 9.24/9.45  thf('208', plain,
% 9.24/9.45      (![X0 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0) = (k1_xboole_0))),
% 9.24/9.45      inference('sup+', [status(thm)], ['202', '207'])).
% 9.24/9.45  thf('209', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 9.24/9.45      inference('sup-', [status(thm)], ['165', '166'])).
% 9.24/9.45  thf('210', plain,
% 9.24/9.45      (![X26 : $i, X27 : $i]:
% 9.24/9.45         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 9.24/9.45          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 9.24/9.45      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.24/9.45  thf('211', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 9.24/9.45           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['209', '210'])).
% 9.24/9.45  thf('212', plain,
% 9.24/9.45      (![X0 : $i]:
% 9.24/9.45         ((k3_subset_1 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0) = (k1_xboole_0))),
% 9.24/9.45      inference('demod', [status(thm)], ['208', '211'])).
% 9.24/9.45  thf('213', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 9.24/9.45      inference('sup-', [status(thm)], ['165', '166'])).
% 9.24/9.45  thf(involutiveness_k3_subset_1, axiom,
% 9.24/9.45    (![A:$i,B:$i]:
% 9.24/9.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.24/9.45       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 9.24/9.45  thf('214', plain,
% 9.24/9.45      (![X30 : $i, X31 : $i]:
% 9.24/9.45         (((k3_subset_1 @ X31 @ (k3_subset_1 @ X31 @ X30)) = (X30))
% 9.24/9.45          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 9.24/9.45      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 9.24/9.45  thf('215', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ 
% 9.24/9.45           (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ X0)) = (X0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['213', '214'])).
% 9.24/9.45  thf('216', plain,
% 9.24/9.45      (![X0 : $i]:
% 9.24/9.45         ((k3_subset_1 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0) = (X0))),
% 9.24/9.45      inference('sup+', [status(thm)], ['212', '215'])).
% 9.24/9.45  thf('217', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['170', '171'])).
% 9.24/9.45  thf('218', plain,
% 9.24/9.45      (![X30 : $i, X31 : $i]:
% 9.24/9.45         (((k3_subset_1 @ X31 @ (k3_subset_1 @ X31 @ X30)) = (X30))
% 9.24/9.45          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 9.24/9.45      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 9.24/9.45  thf('219', plain,
% 9.24/9.45      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['217', '218'])).
% 9.24/9.45  thf('220', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 9.24/9.45      inference('cnf', [status(esa)], [t3_boole])).
% 9.24/9.45  thf('221', plain,
% 9.24/9.45      (![X17 : $i, X18 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.24/9.45           = (k3_xboole_0 @ X17 @ X18))),
% 9.24/9.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.24/9.45  thf('222', plain,
% 9.24/9.45      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 9.24/9.45      inference('sup+', [status(thm)], ['220', '221'])).
% 9.24/9.45  thf('223', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['170', '171'])).
% 9.24/9.45  thf('224', plain,
% 9.24/9.45      (![X26 : $i, X27 : $i]:
% 9.24/9.45         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 9.24/9.45          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 9.24/9.45      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.24/9.45  thf('225', plain,
% 9.24/9.45      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['223', '224'])).
% 9.24/9.45  thf('226', plain,
% 9.24/9.45      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 9.24/9.45      inference('cnf', [status(esa)], [t2_boole])).
% 9.24/9.45  thf('227', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 9.24/9.45      inference('demod', [status(thm)], ['222', '225', '226'])).
% 9.24/9.45  thf('228', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 9.24/9.45      inference('demod', [status(thm)], ['219', '227'])).
% 9.24/9.45  thf('229', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 9.24/9.45      inference('demod', [status(thm)], ['216', '228'])).
% 9.24/9.45  thf('230', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('sup+', [status(thm)], ['2', '3'])).
% 9.24/9.45  thf('231', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 9.24/9.45      inference('sup+', [status(thm)], ['229', '230'])).
% 9.24/9.45  thf('232', plain,
% 9.24/9.45      (![X19 : $i, X20 : $i]:
% 9.24/9.45         ((k2_xboole_0 @ X19 @ (k2_xboole_0 @ X19 @ X20))
% 9.24/9.45           = (k2_xboole_0 @ X19 @ X20))),
% 9.24/9.45      inference('cnf', [status(esa)], [t6_xboole_1])).
% 9.24/9.45  thf('233', plain,
% 9.24/9.45      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 9.24/9.45      inference('sup+', [status(thm)], ['231', '232'])).
% 9.24/9.45  thf('234', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 9.24/9.45      inference('sup+', [status(thm)], ['229', '230'])).
% 9.24/9.45  thf('235', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 9.24/9.45      inference('demod', [status(thm)], ['233', '234'])).
% 9.24/9.45  thf('236', plain,
% 9.24/9.45      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 9.24/9.45          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('demod', [status(thm)], ['201', '235'])).
% 9.24/9.45  thf('237', plain,
% 9.24/9.45      (((k2_pre_topc @ sk_A @ sk_B)
% 9.24/9.45         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45            (k2_tops_1 @ sk_A @ sk_B)))),
% 9.24/9.45      inference('demod', [status(thm)], ['52', '53'])).
% 9.24/9.45  thf('238', plain,
% 9.24/9.45      ((((k2_pre_topc @ sk_A @ sk_B)
% 9.24/9.45          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('sup+', [status(thm)], ['236', '237'])).
% 9.24/9.45  thf('239', plain,
% 9.24/9.45      ((((k4_subset_1 @ sk_B @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 9.24/9.45          = (k2_pre_topc @ sk_A @ sk_B)))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('demod', [status(thm)], ['190', '238'])).
% 9.24/9.45  thf('240', plain,
% 9.24/9.45      ((((sk_B) = (k2_pre_topc @ sk_A @ sk_B)))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('sup+', [status(thm)], ['185', '239'])).
% 9.24/9.45  thf('241', plain,
% 9.24/9.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 9.24/9.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.24/9.45  thf(fc1_tops_1, axiom,
% 9.24/9.45    (![A:$i,B:$i]:
% 9.24/9.45     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 9.24/9.45         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 9.24/9.45       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 9.24/9.45  thf('242', plain,
% 9.24/9.45      (![X49 : $i, X50 : $i]:
% 9.24/9.45         (~ (l1_pre_topc @ X49)
% 9.24/9.45          | ~ (v2_pre_topc @ X49)
% 9.24/9.45          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 9.24/9.45          | (v4_pre_topc @ (k2_pre_topc @ X49 @ X50) @ X49))),
% 9.24/9.45      inference('cnf', [status(esa)], [fc1_tops_1])).
% 9.24/9.45  thf('243', plain,
% 9.24/9.45      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 9.24/9.45        | ~ (v2_pre_topc @ sk_A)
% 9.24/9.45        | ~ (l1_pre_topc @ sk_A))),
% 9.24/9.45      inference('sup-', [status(thm)], ['241', '242'])).
% 9.24/9.45  thf('244', plain, ((v2_pre_topc @ sk_A)),
% 9.24/9.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.24/9.45  thf('245', plain, ((l1_pre_topc @ sk_A)),
% 9.24/9.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.24/9.45  thf('246', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 9.24/9.45      inference('demod', [status(thm)], ['243', '244', '245'])).
% 9.24/9.45  thf('247', plain,
% 9.24/9.45      (((v4_pre_topc @ sk_B @ sk_A))
% 9.24/9.45         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('sup+', [status(thm)], ['240', '246'])).
% 9.24/9.45  thf('248', plain,
% 9.24/9.45      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 9.24/9.45      inference('split', [status(esa)], ['63'])).
% 9.24/9.45  thf('249', plain,
% 9.24/9.45      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 9.24/9.45       ~
% 9.24/9.45       (((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45             (k1_tops_1 @ sk_A @ sk_B))))),
% 9.24/9.45      inference('sup-', [status(thm)], ['247', '248'])).
% 9.24/9.45  thf('250', plain,
% 9.24/9.45      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 9.24/9.45       (((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45             (k1_tops_1 @ sk_A @ sk_B))))),
% 9.24/9.45      inference('split', [status(esa)], ['55'])).
% 9.24/9.45  thf('251', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 9.24/9.45      inference('sat_resolution*', [status(thm)], ['64', '249', '250'])).
% 9.24/9.45  thf('252', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 9.24/9.45      inference('simpl_trail', [status(thm)], ['62', '251'])).
% 9.24/9.45  thf('253', plain,
% 9.24/9.45      (((sk_B)
% 9.24/9.45         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45            (k2_tops_1 @ sk_A @ sk_B)))),
% 9.24/9.45      inference('demod', [status(thm)], ['54', '252'])).
% 9.24/9.45  thf('254', plain,
% 9.24/9.45      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 9.24/9.45         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 9.24/9.45      inference('demod', [status(thm)], ['32', '33', '34'])).
% 9.24/9.45  thf('255', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('sup+', [status(thm)], ['2', '3'])).
% 9.24/9.45  thf('256', plain,
% 9.24/9.45      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 9.24/9.45      inference('demod', [status(thm)], ['49', '253', '254', '255'])).
% 9.24/9.45  thf('257', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['5', '6'])).
% 9.24/9.45  thf('258', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['5', '6'])).
% 9.24/9.45  thf('259', plain,
% 9.24/9.45      (![X2 : $i, X3 : $i, X4 : $i]:
% 9.24/9.45         (~ (r1_tarski @ X2 @ X3)
% 9.24/9.45          | ~ (r1_tarski @ X3 @ X4)
% 9.24/9.45          | (r1_tarski @ X2 @ X4))),
% 9.24/9.45      inference('cnf', [status(esa)], [t1_xboole_1])).
% 9.24/9.45  thf('260', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.24/9.45         ((r1_tarski @ X0 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 9.24/9.45      inference('sup-', [status(thm)], ['258', '259'])).
% 9.24/9.45  thf('261', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.24/9.45         (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 9.24/9.45      inference('sup-', [status(thm)], ['257', '260'])).
% 9.24/9.45  thf('262', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.24/9.45         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 9.24/9.45          | (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 9.24/9.45      inference('sup-', [status(thm)], ['115', '116'])).
% 9.24/9.45  thf('263', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.24/9.45         (r1_tarski @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ X2)),
% 9.24/9.45      inference('sup-', [status(thm)], ['261', '262'])).
% 9.24/9.45  thf('264', plain,
% 9.24/9.45      (![X8 : $i, X9 : $i]:
% 9.24/9.45         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 9.24/9.45      inference('cnf', [status(esa)], [t38_xboole_1])).
% 9.24/9.45  thf('265', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['263', '264'])).
% 9.24/9.45  thf('266', plain,
% 9.24/9.45      (((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0))),
% 9.24/9.45      inference('sup+', [status(thm)], ['256', '265'])).
% 9.24/9.45  thf('267', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('sup+', [status(thm)], ['25', '26'])).
% 9.24/9.45  thf('268', plain,
% 9.24/9.45      (![X17 : $i, X18 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.24/9.45           = (k3_xboole_0 @ X17 @ X18))),
% 9.24/9.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.24/9.45  thf('269', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['41', '42'])).
% 9.24/9.45  thf('270', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 9.24/9.45      inference('sup+', [status(thm)], ['268', '269'])).
% 9.24/9.45  thf('271', plain,
% 9.24/9.45      (![X26 : $i, X27 : $i]:
% 9.24/9.45         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 9.24/9.45          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 9.24/9.45      inference('cnf', [status(esa)], [d5_subset_1])).
% 9.24/9.45  thf('272', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 9.24/9.45           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 9.24/9.45      inference('sup-', [status(thm)], ['270', '271'])).
% 9.24/9.45  thf('273', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['41', '42'])).
% 9.24/9.45  thf('274', plain,
% 9.24/9.45      (![X30 : $i, X31 : $i]:
% 9.24/9.45         (((k3_subset_1 @ X31 @ (k3_subset_1 @ X31 @ X30)) = (X30))
% 9.24/9.45          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 9.24/9.45      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 9.24/9.45  thf('275', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 9.24/9.45           = (k4_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('sup-', [status(thm)], ['273', '274'])).
% 9.24/9.45  thf('276', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 9.24/9.45           = (k3_xboole_0 @ X1 @ X0))),
% 9.24/9.45      inference('sup+', [status(thm)], ['72', '73'])).
% 9.24/9.45  thf('277', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 9.24/9.45           = (k4_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('demod', [status(thm)], ['275', '276'])).
% 9.24/9.45  thf('278', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X0 @ X1)
% 9.24/9.45           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 9.24/9.45      inference('demod', [status(thm)], ['272', '277'])).
% 9.24/9.45  thf('279', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X0 @ X1)
% 9.24/9.45           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 9.24/9.45      inference('sup+', [status(thm)], ['267', '278'])).
% 9.24/9.45  thf('280', plain,
% 9.24/9.45      (![X17 : $i, X18 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.24/9.45           = (k3_xboole_0 @ X17 @ X18))),
% 9.24/9.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.24/9.45  thf('281', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 9.24/9.45           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1)))),
% 9.24/9.45      inference('sup+', [status(thm)], ['279', '280'])).
% 9.24/9.45  thf('282', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('sup+', [status(thm)], ['25', '26'])).
% 9.24/9.45  thf('283', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 9.24/9.45           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 9.24/9.45      inference('sup+', [status(thm)], ['156', '157'])).
% 9.24/9.45  thf('284', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 9.24/9.45           = (k4_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('demod', [status(thm)], ['275', '276'])).
% 9.24/9.45  thf('285', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 9.24/9.45           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 9.24/9.45      inference('sup+', [status(thm)], ['283', '284'])).
% 9.24/9.45  thf('286', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 9.24/9.45           = (k3_xboole_0 @ X1 @ X0))),
% 9.24/9.45      inference('sup+', [status(thm)], ['72', '73'])).
% 9.24/9.45  thf('287', plain,
% 9.24/9.45      (![X17 : $i, X18 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.24/9.45           = (k3_xboole_0 @ X17 @ X18))),
% 9.24/9.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.24/9.45  thf('288', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 9.24/9.45           = (k3_xboole_0 @ X1 @ X0))),
% 9.24/9.45      inference('demod', [status(thm)], ['285', '286', '287'])).
% 9.24/9.45  thf('289', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X0 @ X1)
% 9.24/9.45           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 9.24/9.45      inference('sup+', [status(thm)], ['27', '28'])).
% 9.24/9.45  thf('290', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 9.24/9.45           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 9.24/9.45      inference('sup+', [status(thm)], ['288', '289'])).
% 9.24/9.45  thf('291', plain,
% 9.24/9.45      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['223', '224'])).
% 9.24/9.45  thf('292', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 9.24/9.45      inference('demod', [status(thm)], ['222', '225', '226'])).
% 9.24/9.45  thf('293', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 9.24/9.45      inference('demod', [status(thm)], ['291', '292'])).
% 9.24/9.45  thf('294', plain,
% 9.24/9.45      (![X17 : $i, X18 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.24/9.45           = (k3_xboole_0 @ X17 @ X18))),
% 9.24/9.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.24/9.45  thf('295', plain,
% 9.24/9.45      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 9.24/9.45      inference('sup+', [status(thm)], ['293', '294'])).
% 9.24/9.45  thf('296', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 9.24/9.45      inference('cnf', [status(esa)], [t3_boole])).
% 9.24/9.45  thf('297', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 9.24/9.45      inference('demod', [status(thm)], ['295', '296'])).
% 9.24/9.45  thf('298', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X0 @ X1)
% 9.24/9.45           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 9.24/9.45      inference('cnf', [status(esa)], [t100_xboole_1])).
% 9.24/9.45  thf('299', plain,
% 9.24/9.45      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 9.24/9.45      inference('sup+', [status(thm)], ['297', '298'])).
% 9.24/9.45  thf('300', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 9.24/9.45      inference('demod', [status(thm)], ['291', '292'])).
% 9.24/9.45  thf('301', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 9.24/9.45      inference('sup+', [status(thm)], ['299', '300'])).
% 9.24/9.45  thf('302', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 9.24/9.45      inference('demod', [status(thm)], ['290', '301'])).
% 9.24/9.45  thf('303', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 9.24/9.45      inference('sup+', [status(thm)], ['282', '302'])).
% 9.24/9.45  thf('304', plain,
% 9.24/9.45      (![X17 : $i, X18 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 9.24/9.45           = (k3_xboole_0 @ X17 @ X18))),
% 9.24/9.45      inference('cnf', [status(esa)], [t48_xboole_1])).
% 9.24/9.45  thf('305', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 9.24/9.45           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 9.24/9.45      inference('sup+', [status(thm)], ['303', '304'])).
% 9.24/9.45  thf('306', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 9.24/9.45      inference('cnf', [status(esa)], [t3_boole])).
% 9.24/9.45  thf('307', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('sup+', [status(thm)], ['25', '26'])).
% 9.24/9.45  thf('308', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k3_xboole_0 @ X1 @ X0)
% 9.24/9.45           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 9.24/9.45      inference('demod', [status(thm)], ['305', '306', '307'])).
% 9.24/9.45  thf('309', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 9.24/9.45           = (k3_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('demod', [status(thm)], ['281', '308'])).
% 9.24/9.45  thf('310', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['170', '171'])).
% 9.24/9.45  thf('311', plain,
% 9.24/9.45      (![X35 : $i, X36 : $i, X37 : $i]:
% 9.24/9.45         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 9.24/9.45          | ((k7_subset_1 @ X36 @ X35 @ X37) = (k4_xboole_0 @ X35 @ X37)))),
% 9.24/9.45      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 9.24/9.45  thf('312', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('sup-', [status(thm)], ['310', '311'])).
% 9.24/9.45  thf('313', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k7_subset_1 @ X0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 9.24/9.45           = (k3_xboole_0 @ X1 @ X0))),
% 9.24/9.45      inference('sup+', [status(thm)], ['309', '312'])).
% 9.24/9.45  thf('314', plain,
% 9.24/9.45      (((k7_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 9.24/9.45         k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 9.24/9.45      inference('sup+', [status(thm)], ['266', '313'])).
% 9.24/9.45  thf('315', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('sup-', [status(thm)], ['310', '311'])).
% 9.24/9.45  thf('316', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 9.24/9.45      inference('cnf', [status(esa)], [t3_boole])).
% 9.24/9.45  thf('317', plain,
% 9.24/9.45      (![X0 : $i]: ((k7_subset_1 @ X0 @ X0 @ k1_xboole_0) = (X0))),
% 9.24/9.45      inference('sup+', [status(thm)], ['315', '316'])).
% 9.24/9.45  thf('318', plain,
% 9.24/9.45      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 9.24/9.45         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 9.24/9.45      inference('demod', [status(thm)], ['107', '137'])).
% 9.24/9.45  thf('319', plain,
% 9.24/9.45      (((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 9.24/9.45      inference('demod', [status(thm)], ['314', '317', '318'])).
% 9.24/9.45  thf('320', plain,
% 9.24/9.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45              (k1_tops_1 @ sk_A @ sk_B))))
% 9.24/9.45         <= (~
% 9.24/9.45             (((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('split', [status(esa)], ['63'])).
% 9.24/9.45  thf('321', plain,
% 9.24/9.45      (![X0 : $i]:
% 9.24/9.45         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 9.24/9.45           = (k4_xboole_0 @ sk_B @ X0))),
% 9.24/9.45      inference('sup-', [status(thm)], ['78', '79'])).
% 9.24/9.45  thf('322', plain,
% 9.24/9.45      (((k1_tops_1 @ sk_A @ sk_B)
% 9.24/9.45         = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 9.24/9.45      inference('demod', [status(thm)], ['134', '135', '136'])).
% 9.24/9.45  thf('323', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('sup-', [status(thm)], ['310', '311'])).
% 9.24/9.45  thf('324', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k4_xboole_0 @ X0 @ X1)
% 9.24/9.45           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 9.24/9.45      inference('cnf', [status(esa)], [t100_xboole_1])).
% 9.24/9.45  thf('325', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k7_subset_1 @ X1 @ X1 @ X0)
% 9.24/9.45           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 9.24/9.45      inference('sup+', [status(thm)], ['323', '324'])).
% 9.24/9.45  thf('326', plain,
% 9.24/9.45      (((k7_subset_1 @ sk_B @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 9.24/9.45         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 9.24/9.45      inference('sup+', [status(thm)], ['322', '325'])).
% 9.24/9.45  thf('327', plain,
% 9.24/9.45      (![X0 : $i, X1 : $i]:
% 9.24/9.45         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 9.24/9.45      inference('sup-', [status(thm)], ['310', '311'])).
% 9.24/9.45  thf('328', plain,
% 9.24/9.45      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 9.24/9.45         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 9.24/9.45      inference('demod', [status(thm)], ['326', '327'])).
% 9.24/9.45  thf('329', plain,
% 9.24/9.45      ((((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45          != (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 9.24/9.45         <= (~
% 9.24/9.45             (((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 9.24/9.45      inference('demod', [status(thm)], ['320', '321', '328'])).
% 9.24/9.45  thf('330', plain,
% 9.24/9.45      (~
% 9.24/9.45       (((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 9.24/9.45             (k1_tops_1 @ sk_A @ sk_B))))),
% 9.24/9.45      inference('sat_resolution*', [status(thm)], ['64', '249'])).
% 9.24/9.45  thf('331', plain,
% 9.24/9.45      (((k2_tops_1 @ sk_A @ sk_B)
% 9.24/9.45         != (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 9.24/9.45      inference('simpl_trail', [status(thm)], ['329', '330'])).
% 9.24/9.45  thf('332', plain, ($false),
% 9.24/9.45      inference('simplify_reflect-', [status(thm)], ['319', '331'])).
% 9.24/9.45  
% 9.24/9.45  % SZS output end Refutation
% 9.24/9.45  
% 9.24/9.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
