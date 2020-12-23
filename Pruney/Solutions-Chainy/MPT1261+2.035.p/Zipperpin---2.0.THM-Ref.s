%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nZv7crulB3

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:42 EST 2020

% Result     : Theorem 3.78s
% Output     : Refutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :  291 (1916 expanded)
%              Number of leaves         :   50 ( 645 expanded)
%              Depth                    :   24
%              Number of atoms          : 2511 (16590 expanded)
%              Number of equality atoms :  207 (1265 expanded)
%              Maximal formula depth    :   12 (   6 average)

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

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X42: $i,X43: $i] :
      ( ( r1_tarski @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','13'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
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
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
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
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('67',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( ( k7_subset_1 @ X36 @ X35 @ X37 )
        = ( k4_xboole_0 @ X35 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['55'])).

thf('70',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('72',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('74',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) @ sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('76',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ X0 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X42: $i,X44: $i] :
      ( ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( r1_tarski @ X42 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('78',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['65','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('81',plain,(
    ! [X42: $i,X44: $i] :
      ( ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( r1_tarski @ X42 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('82',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) )
      | ( ( k4_subset_1 @ X33 @ X32 @ X34 )
        = ( k2_xboole_0 @ X32 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ X1 )
        = ( k2_xboole_0 @ sk_B @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( k4_subset_1 @ ( k2_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['79','84'])).

thf('86',plain,
    ( ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('87',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('88',plain,
    ( ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    = ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('91',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    = ( k2_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('93',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X42: $i,X44: $i] :
      ( ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( r1_tarski @ X42 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('96',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('97',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('100',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('102',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('105',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['100','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('109',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) )
      | ( ( k4_subset_1 @ X33 @ X32 @ X34 )
        = ( k2_xboole_0 @ X32 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ X0 @ X1 )
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['107','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('113',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k4_subset_1 @ X38 @ X39 @ ( k3_subset_1 @ X38 @ X39 ) )
        = ( k2_subset_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('114',plain,(
    ! [X25: $i] :
      ( ( k2_subset_1 @ X25 )
      = X25 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('115',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k4_subset_1 @ X38 @ X39 @ ( k3_subset_1 @ X38 @ X39 ) )
        = X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['112','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['111','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['91','121'])).

thf('123',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ X0 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('125',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ X0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['123','126'])).

thf('128',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('129',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('131',plain,
    ( ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('133',plain,
    ( ( ( k2_xboole_0 @ k1_xboole_0 @ sk_B )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('135',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['85','122','135'])).

thf('137',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('138',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('140',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( l1_pre_topc @ X49 )
      | ~ ( v2_pre_topc @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X49 @ X50 ) @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('141',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['138','144'])).

thf('146',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['63'])).

thf('147',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['55'])).

thf('149',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['64','147','148'])).

thf('150',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['62','149'])).

thf('151',plain,
    ( sk_B
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','150'])).

thf('152',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('154',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','151','152','153'])).

thf('155',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('156',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['111','118'])).

thf('159',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      | ~ ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['157','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('163',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('166',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['164','167'])).

thf('169',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('171',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('173',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['168','173'])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['161','174'])).

thf('176',plain,
    ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['154','175'])).

thf('177',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('179',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('180',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['178','181'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('183',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X31 @ ( k3_subset_1 @ X31 @ X30 ) )
        = X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('187',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X31 @ ( k3_subset_1 @ X31 @ X30 ) )
        = X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('190',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('193',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['188','193'])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['185','194'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['184','195'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['177','196'])).

thf('198',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['188','193'])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['197','198','199'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['188','193'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['200','201'])).

thf('203',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['184','195'])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('206',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( ( k7_subset_1 @ X36 @ X35 @ X37 )
        = ( k4_xboole_0 @ X35 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['204','207'])).

thf('209',plain,
    ( ( k7_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['176','208'])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('211',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['210','211'])).

thf('213',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('214',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( ( k1_tops_1 @ X56 @ X55 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X56 ) @ X55 @ ( k2_tops_1 @ X56 @ X55 ) ) )
      | ~ ( l1_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('215',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('218',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['215','216','217'])).

thf('219',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('220',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['202','203'])).

thf('221',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['219','220'])).

thf('222',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['197','198','199'])).

thf('223',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['221','222'])).

thf('224',plain,
    ( ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['218','223'])).

thf('225',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('226',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['224','225'])).

thf('227',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['209','212','226'])).

thf('228',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['215','216','217'])).

thf('229',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('230',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['228','229'])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('232',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['63'])).

thf('233',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['231','232'])).

thf('234',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['230','233'])).

thf('235',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['224','225'])).

thf('236',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['234','235'])).

thf('237',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['64','147'])).

thf('238',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['236','237'])).

thf('239',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['227','238'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nZv7crulB3
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:31:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 3.78/3.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.78/3.96  % Solved by: fo/fo7.sh
% 3.78/3.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.78/3.96  % done 9824 iterations in 3.517s
% 3.78/3.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.78/3.96  % SZS output start Refutation
% 3.78/3.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.78/3.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.78/3.96  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 3.78/3.96  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 3.78/3.96  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 3.78/3.96  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 3.78/3.96  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 3.78/3.96  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 3.78/3.96  thf(sk_B_type, type, sk_B: $i).
% 3.78/3.96  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 3.78/3.96  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 3.78/3.96  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 3.78/3.96  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 3.78/3.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.78/3.96  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 3.78/3.96  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.78/3.96  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.78/3.96  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.78/3.96  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.78/3.96  thf(sk_A_type, type, sk_A: $i).
% 3.78/3.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.78/3.96  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 3.78/3.96  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 3.78/3.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.78/3.96  thf(commutativity_k2_tarski, axiom,
% 3.78/3.96    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 3.78/3.96  thf('0', plain,
% 3.78/3.96      (![X21 : $i, X22 : $i]:
% 3.78/3.96         ((k2_tarski @ X22 @ X21) = (k2_tarski @ X21 @ X22))),
% 3.78/3.96      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 3.78/3.96  thf(l51_zfmisc_1, axiom,
% 3.78/3.96    (![A:$i,B:$i]:
% 3.78/3.96     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.78/3.96  thf('1', plain,
% 3.78/3.96      (![X23 : $i, X24 : $i]:
% 3.78/3.96         ((k3_tarski @ (k2_tarski @ X23 @ X24)) = (k2_xboole_0 @ X23 @ X24))),
% 3.78/3.96      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.78/3.96  thf('2', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 3.78/3.96      inference('sup+', [status(thm)], ['0', '1'])).
% 3.78/3.96  thf('3', plain,
% 3.78/3.96      (![X23 : $i, X24 : $i]:
% 3.78/3.96         ((k3_tarski @ (k2_tarski @ X23 @ X24)) = (k2_xboole_0 @ X23 @ X24))),
% 3.78/3.96      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.78/3.96  thf('4', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.78/3.96      inference('sup+', [status(thm)], ['2', '3'])).
% 3.78/3.96  thf(t77_tops_1, conjecture,
% 3.78/3.96    (![A:$i]:
% 3.78/3.96     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.78/3.96       ( ![B:$i]:
% 3.78/3.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.78/3.96           ( ( v4_pre_topc @ B @ A ) <=>
% 3.78/3.96             ( ( k2_tops_1 @ A @ B ) =
% 3.78/3.96               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 3.78/3.96  thf(zf_stmt_0, negated_conjecture,
% 3.78/3.96    (~( ![A:$i]:
% 3.78/3.96        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 3.78/3.96          ( ![B:$i]:
% 3.78/3.96            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.78/3.96              ( ( v4_pre_topc @ B @ A ) <=>
% 3.78/3.96                ( ( k2_tops_1 @ A @ B ) =
% 3.78/3.96                  ( k7_subset_1 @
% 3.78/3.96                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 3.78/3.96    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 3.78/3.96  thf('5', plain,
% 3.78/3.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.78/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.78/3.96  thf(t3_subset, axiom,
% 3.78/3.96    (![A:$i,B:$i]:
% 3.78/3.96     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.78/3.96  thf('6', plain,
% 3.78/3.96      (![X42 : $i, X43 : $i]:
% 3.78/3.96         ((r1_tarski @ X42 @ X43) | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43)))),
% 3.78/3.96      inference('cnf', [status(esa)], [t3_subset])).
% 3.78/3.96  thf('7', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 3.78/3.96      inference('sup-', [status(thm)], ['5', '6'])).
% 3.78/3.96  thf(t36_xboole_1, axiom,
% 3.78/3.96    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 3.78/3.96  thf('8', plain,
% 3.78/3.96      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 3.78/3.96      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.78/3.96  thf(t1_xboole_1, axiom,
% 3.78/3.96    (![A:$i,B:$i,C:$i]:
% 3.78/3.96     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 3.78/3.96       ( r1_tarski @ A @ C ) ))).
% 3.78/3.96  thf('9', plain,
% 3.78/3.96      (![X2 : $i, X3 : $i, X4 : $i]:
% 3.78/3.96         (~ (r1_tarski @ X2 @ X3)
% 3.78/3.96          | ~ (r1_tarski @ X3 @ X4)
% 3.78/3.96          | (r1_tarski @ X2 @ X4))),
% 3.78/3.96      inference('cnf', [status(esa)], [t1_xboole_1])).
% 3.78/3.96  thf('10', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.78/3.96         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 3.78/3.96      inference('sup-', [status(thm)], ['8', '9'])).
% 3.78/3.96  thf('11', plain,
% 3.78/3.96      (![X0 : $i]:
% 3.78/3.96         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 3.78/3.96      inference('sup-', [status(thm)], ['7', '10'])).
% 3.78/3.96  thf(t44_xboole_1, axiom,
% 3.78/3.96    (![A:$i,B:$i,C:$i]:
% 3.78/3.96     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 3.78/3.96       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.78/3.96  thf('12', plain,
% 3.78/3.96      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.78/3.96         ((r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 3.78/3.96          | ~ (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18))),
% 3.78/3.96      inference('cnf', [status(esa)], [t44_xboole_1])).
% 3.78/3.96  thf('13', plain,
% 3.78/3.96      (![X0 : $i]:
% 3.78/3.96         (r1_tarski @ sk_B @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))),
% 3.78/3.96      inference('sup-', [status(thm)], ['11', '12'])).
% 3.78/3.96  thf('14', plain,
% 3.78/3.96      (![X0 : $i]:
% 3.78/3.96         (r1_tarski @ sk_B @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))),
% 3.78/3.96      inference('sup+', [status(thm)], ['4', '13'])).
% 3.78/3.96  thf(t43_xboole_1, axiom,
% 3.78/3.96    (![A:$i,B:$i,C:$i]:
% 3.78/3.96     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 3.78/3.96       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 3.78/3.96  thf('15', plain,
% 3.78/3.96      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.78/3.96         ((r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 3.78/3.96          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 3.78/3.96      inference('cnf', [status(esa)], [t43_xboole_1])).
% 3.78/3.96  thf('16', plain,
% 3.78/3.96      (![X0 : $i]:
% 3.78/3.96         (r1_tarski @ (k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)),
% 3.78/3.96      inference('sup-', [status(thm)], ['14', '15'])).
% 3.78/3.96  thf(t38_xboole_1, axiom,
% 3.78/3.96    (![A:$i,B:$i]:
% 3.78/3.96     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 3.78/3.96       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.78/3.96  thf('17', plain,
% 3.78/3.96      (![X8 : $i, X9 : $i]:
% 3.78/3.96         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 3.78/3.96      inference('cnf', [status(esa)], [t38_xboole_1])).
% 3.78/3.96  thf('18', plain,
% 3.78/3.96      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 3.78/3.96      inference('sup-', [status(thm)], ['16', '17'])).
% 3.78/3.96  thf(t48_xboole_1, axiom,
% 3.78/3.96    (![A:$i,B:$i]:
% 3.78/3.96     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.78/3.96  thf('19', plain,
% 3.78/3.96      (![X19 : $i, X20 : $i]:
% 3.78/3.96         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 3.78/3.96           = (k3_xboole_0 @ X19 @ X20))),
% 3.78/3.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.78/3.96  thf('20', plain,
% 3.78/3.96      (((k4_xboole_0 @ sk_B @ k1_xboole_0)
% 3.78/3.96         = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 3.78/3.96      inference('sup+', [status(thm)], ['18', '19'])).
% 3.78/3.96  thf(t3_boole, axiom,
% 3.78/3.96    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.78/3.96  thf('21', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 3.78/3.96      inference('cnf', [status(esa)], [t3_boole])).
% 3.78/3.96  thf('22', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 3.78/3.96      inference('demod', [status(thm)], ['20', '21'])).
% 3.78/3.96  thf('23', plain,
% 3.78/3.96      (![X21 : $i, X22 : $i]:
% 3.78/3.96         ((k2_tarski @ X22 @ X21) = (k2_tarski @ X21 @ X22))),
% 3.78/3.96      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 3.78/3.96  thf(t12_setfam_1, axiom,
% 3.78/3.96    (![A:$i,B:$i]:
% 3.78/3.96     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 3.78/3.96  thf('24', plain,
% 3.78/3.96      (![X40 : $i, X41 : $i]:
% 3.78/3.96         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 3.78/3.96      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.78/3.96  thf('25', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 3.78/3.96      inference('sup+', [status(thm)], ['23', '24'])).
% 3.78/3.96  thf('26', plain,
% 3.78/3.96      (![X40 : $i, X41 : $i]:
% 3.78/3.96         ((k1_setfam_1 @ (k2_tarski @ X40 @ X41)) = (k3_xboole_0 @ X40 @ X41))),
% 3.78/3.96      inference('cnf', [status(esa)], [t12_setfam_1])).
% 3.78/3.96  thf('27', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.78/3.96      inference('sup+', [status(thm)], ['25', '26'])).
% 3.78/3.96  thf(t100_xboole_1, axiom,
% 3.78/3.96    (![A:$i,B:$i]:
% 3.78/3.96     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.78/3.96  thf('28', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k4_xboole_0 @ X0 @ X1)
% 3.78/3.96           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 3.78/3.96      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.78/3.96  thf('29', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k4_xboole_0 @ X0 @ X1)
% 3.78/3.96           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.78/3.96      inference('sup+', [status(thm)], ['27', '28'])).
% 3.78/3.96  thf('30', plain,
% 3.78/3.96      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 3.78/3.96         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 3.78/3.96      inference('sup+', [status(thm)], ['22', '29'])).
% 3.78/3.96  thf('31', plain,
% 3.78/3.96      (![X19 : $i, X20 : $i]:
% 3.78/3.96         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 3.78/3.96           = (k3_xboole_0 @ X19 @ X20))),
% 3.78/3.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.78/3.96  thf('32', plain,
% 3.78/3.96      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 3.78/3.96         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 3.78/3.96         = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 3.78/3.96      inference('sup+', [status(thm)], ['30', '31'])).
% 3.78/3.96  thf('33', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.78/3.96      inference('sup+', [status(thm)], ['25', '26'])).
% 3.78/3.96  thf('34', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 3.78/3.96      inference('demod', [status(thm)], ['20', '21'])).
% 3.78/3.96  thf('35', plain,
% 3.78/3.96      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 3.78/3.96         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 3.78/3.96      inference('demod', [status(thm)], ['32', '33', '34'])).
% 3.78/3.96  thf('36', plain,
% 3.78/3.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.78/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.78/3.96  thf(dt_k2_tops_1, axiom,
% 3.78/3.96    (![A:$i,B:$i]:
% 3.78/3.96     ( ( ( l1_pre_topc @ A ) & 
% 3.78/3.96         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.78/3.96       ( m1_subset_1 @
% 3.78/3.96         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 3.78/3.96  thf('37', plain,
% 3.78/3.96      (![X47 : $i, X48 : $i]:
% 3.78/3.96         (~ (l1_pre_topc @ X47)
% 3.78/3.96          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X47)))
% 3.78/3.96          | (m1_subset_1 @ (k2_tops_1 @ X47 @ X48) @ 
% 3.78/3.96             (k1_zfmisc_1 @ (u1_struct_0 @ X47))))),
% 3.78/3.96      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 3.78/3.96  thf('38', plain,
% 3.78/3.96      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.78/3.96         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 3.78/3.96        | ~ (l1_pre_topc @ sk_A))),
% 3.78/3.96      inference('sup-', [status(thm)], ['36', '37'])).
% 3.78/3.96  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 3.78/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.78/3.96  thf('40', plain,
% 3.78/3.96      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.78/3.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.78/3.96      inference('demod', [status(thm)], ['38', '39'])).
% 3.78/3.96  thf('41', plain,
% 3.78/3.96      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 3.78/3.96      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.78/3.96  thf('42', plain,
% 3.78/3.96      (![X42 : $i, X44 : $i]:
% 3.78/3.96         ((m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X44)) | ~ (r1_tarski @ X42 @ X44))),
% 3.78/3.96      inference('cnf', [status(esa)], [t3_subset])).
% 3.78/3.96  thf('43', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 3.78/3.96      inference('sup-', [status(thm)], ['41', '42'])).
% 3.78/3.96  thf(redefinition_k4_subset_1, axiom,
% 3.78/3.96    (![A:$i,B:$i,C:$i]:
% 3.78/3.96     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 3.78/3.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 3.78/3.96       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 3.78/3.96  thf('44', plain,
% 3.78/3.96      (![X32 : $i, X33 : $i, X34 : $i]:
% 3.78/3.96         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 3.78/3.96          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33))
% 3.78/3.96          | ((k4_subset_1 @ X33 @ X32 @ X34) = (k2_xboole_0 @ X32 @ X34)))),
% 3.78/3.96      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 3.78/3.96  thf('45', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.78/3.96         (((k4_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 3.78/3.96            = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))
% 3.78/3.96          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0)))),
% 3.78/3.96      inference('sup-', [status(thm)], ['43', '44'])).
% 3.78/3.96  thf('46', plain,
% 3.78/3.96      (![X0 : $i]:
% 3.78/3.96         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.78/3.96           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 3.78/3.96           (k2_tops_1 @ sk_A @ sk_B))
% 3.78/3.96           = (k2_xboole_0 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 3.78/3.96              (k2_tops_1 @ sk_A @ sk_B)))),
% 3.78/3.96      inference('sup-', [status(thm)], ['40', '45'])).
% 3.78/3.96  thf('47', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.78/3.96      inference('sup+', [status(thm)], ['2', '3'])).
% 3.78/3.96  thf('48', plain,
% 3.78/3.96      (![X0 : $i]:
% 3.78/3.96         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 3.78/3.96           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 3.78/3.96           (k2_tops_1 @ sk_A @ sk_B))
% 3.78/3.96           = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.78/3.96              (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 3.78/3.96      inference('demod', [status(thm)], ['46', '47'])).
% 3.78/3.96  thf('49', plain,
% 3.78/3.96      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 3.78/3.96         = (k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.78/3.96            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 3.78/3.96             (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 3.78/3.96      inference('sup+', [status(thm)], ['35', '48'])).
% 3.78/3.96  thf('50', plain,
% 3.78/3.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.78/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.78/3.96  thf(t65_tops_1, axiom,
% 3.78/3.96    (![A:$i]:
% 3.78/3.96     ( ( l1_pre_topc @ A ) =>
% 3.78/3.96       ( ![B:$i]:
% 3.78/3.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.78/3.96           ( ( k2_pre_topc @ A @ B ) =
% 3.78/3.96             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 3.78/3.96  thf('51', plain,
% 3.78/3.96      (![X53 : $i, X54 : $i]:
% 3.78/3.96         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 3.78/3.96          | ((k2_pre_topc @ X54 @ X53)
% 3.78/3.96              = (k4_subset_1 @ (u1_struct_0 @ X54) @ X53 @ 
% 3.78/3.96                 (k2_tops_1 @ X54 @ X53)))
% 3.78/3.96          | ~ (l1_pre_topc @ X54))),
% 3.78/3.96      inference('cnf', [status(esa)], [t65_tops_1])).
% 3.78/3.96  thf('52', plain,
% 3.78/3.96      ((~ (l1_pre_topc @ sk_A)
% 3.78/3.96        | ((k2_pre_topc @ sk_A @ sk_B)
% 3.78/3.96            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96               (k2_tops_1 @ sk_A @ sk_B))))),
% 3.78/3.96      inference('sup-', [status(thm)], ['50', '51'])).
% 3.78/3.96  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 3.78/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.78/3.96  thf('54', plain,
% 3.78/3.96      (((k2_pre_topc @ sk_A @ sk_B)
% 3.78/3.96         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96            (k2_tops_1 @ sk_A @ sk_B)))),
% 3.78/3.96      inference('demod', [status(thm)], ['52', '53'])).
% 3.78/3.96  thf('55', plain,
% 3.78/3.96      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96             (k1_tops_1 @ sk_A @ sk_B)))
% 3.78/3.96        | (v4_pre_topc @ sk_B @ sk_A))),
% 3.78/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.78/3.96  thf('56', plain,
% 3.78/3.96      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 3.78/3.96      inference('split', [status(esa)], ['55'])).
% 3.78/3.96  thf('57', plain,
% 3.78/3.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.78/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.78/3.96  thf(t52_pre_topc, axiom,
% 3.78/3.96    (![A:$i]:
% 3.78/3.96     ( ( l1_pre_topc @ A ) =>
% 3.78/3.96       ( ![B:$i]:
% 3.78/3.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.78/3.96           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 3.78/3.96             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 3.78/3.96               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 3.78/3.96  thf('58', plain,
% 3.78/3.96      (![X45 : $i, X46 : $i]:
% 3.78/3.96         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 3.78/3.96          | ~ (v4_pre_topc @ X45 @ X46)
% 3.78/3.96          | ((k2_pre_topc @ X46 @ X45) = (X45))
% 3.78/3.96          | ~ (l1_pre_topc @ X46))),
% 3.78/3.96      inference('cnf', [status(esa)], [t52_pre_topc])).
% 3.78/3.96  thf('59', plain,
% 3.78/3.96      ((~ (l1_pre_topc @ sk_A)
% 3.78/3.96        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 3.78/3.96        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 3.78/3.96      inference('sup-', [status(thm)], ['57', '58'])).
% 3.78/3.96  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 3.78/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.78/3.96  thf('61', plain,
% 3.78/3.96      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 3.78/3.96      inference('demod', [status(thm)], ['59', '60'])).
% 3.78/3.96  thf('62', plain,
% 3.78/3.96      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 3.78/3.96         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 3.78/3.96      inference('sup-', [status(thm)], ['56', '61'])).
% 3.78/3.96  thf('63', plain,
% 3.78/3.96      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96              (k1_tops_1 @ sk_A @ sk_B)))
% 3.78/3.96        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 3.78/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.78/3.96  thf('64', plain,
% 3.78/3.96      (~
% 3.78/3.96       (((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 3.78/3.96       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 3.78/3.96      inference('split', [status(esa)], ['63'])).
% 3.78/3.96  thf('65', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.78/3.96      inference('sup+', [status(thm)], ['2', '3'])).
% 3.78/3.96  thf('66', plain,
% 3.78/3.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.78/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.78/3.96  thf(redefinition_k7_subset_1, axiom,
% 3.78/3.96    (![A:$i,B:$i,C:$i]:
% 3.78/3.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.78/3.96       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 3.78/3.96  thf('67', plain,
% 3.78/3.96      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.78/3.96         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 3.78/3.96          | ((k7_subset_1 @ X36 @ X35 @ X37) = (k4_xboole_0 @ X35 @ X37)))),
% 3.78/3.96      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 3.78/3.96  thf('68', plain,
% 3.78/3.96      (![X0 : $i]:
% 3.78/3.96         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 3.78/3.96           = (k4_xboole_0 @ sk_B @ X0))),
% 3.78/3.96      inference('sup-', [status(thm)], ['66', '67'])).
% 3.78/3.96  thf('69', plain,
% 3.78/3.96      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96             (k1_tops_1 @ sk_A @ sk_B))))
% 3.78/3.96         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.78/3.96      inference('split', [status(esa)], ['55'])).
% 3.78/3.96  thf('70', plain,
% 3.78/3.96      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 3.78/3.96         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.78/3.96      inference('sup+', [status(thm)], ['68', '69'])).
% 3.78/3.96  thf('71', plain,
% 3.78/3.96      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 3.78/3.96      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.78/3.96  thf('72', plain,
% 3.78/3.96      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 3.78/3.96         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.78/3.96      inference('sup+', [status(thm)], ['70', '71'])).
% 3.78/3.96  thf('73', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.78/3.96         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 3.78/3.96      inference('sup-', [status(thm)], ['8', '9'])).
% 3.78/3.96  thf('74', plain,
% 3.78/3.96      ((![X0 : $i]:
% 3.78/3.96          (r1_tarski @ (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0) @ sk_B))
% 3.78/3.96         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.78/3.96      inference('sup-', [status(thm)], ['72', '73'])).
% 3.78/3.96  thf('75', plain,
% 3.78/3.96      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.78/3.96         ((r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 3.78/3.96          | ~ (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18))),
% 3.78/3.96      inference('cnf', [status(esa)], [t44_xboole_1])).
% 3.78/3.96  thf('76', plain,
% 3.78/3.96      ((![X0 : $i]:
% 3.78/3.96          (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_xboole_0 @ X0 @ sk_B)))
% 3.78/3.96         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.78/3.96      inference('sup-', [status(thm)], ['74', '75'])).
% 3.78/3.96  thf('77', plain,
% 3.78/3.96      (![X42 : $i, X44 : $i]:
% 3.78/3.96         ((m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X44)) | ~ (r1_tarski @ X42 @ X44))),
% 3.78/3.96      inference('cnf', [status(esa)], [t3_subset])).
% 3.78/3.96  thf('78', plain,
% 3.78/3.96      ((![X0 : $i]:
% 3.78/3.96          (m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.78/3.96           (k1_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_B))))
% 3.78/3.96         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.78/3.96      inference('sup-', [status(thm)], ['76', '77'])).
% 3.78/3.96  thf('79', plain,
% 3.78/3.96      ((![X0 : $i]:
% 3.78/3.96          (m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.78/3.96           (k1_zfmisc_1 @ (k2_xboole_0 @ sk_B @ X0))))
% 3.78/3.96         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.78/3.96      inference('sup+', [status(thm)], ['65', '78'])).
% 3.78/3.96  thf('80', plain,
% 3.78/3.96      (![X0 : $i]:
% 3.78/3.96         (r1_tarski @ sk_B @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))),
% 3.78/3.96      inference('sup-', [status(thm)], ['11', '12'])).
% 3.78/3.96  thf('81', plain,
% 3.78/3.96      (![X42 : $i, X44 : $i]:
% 3.78/3.96         ((m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X44)) | ~ (r1_tarski @ X42 @ X44))),
% 3.78/3.96      inference('cnf', [status(esa)], [t3_subset])).
% 3.78/3.96  thf('82', plain,
% 3.78/3.96      (![X0 : $i]:
% 3.78/3.96         (m1_subset_1 @ sk_B @ 
% 3.78/3.96          (k1_zfmisc_1 @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A))))),
% 3.78/3.96      inference('sup-', [status(thm)], ['80', '81'])).
% 3.78/3.96  thf('83', plain,
% 3.78/3.96      (![X32 : $i, X33 : $i, X34 : $i]:
% 3.78/3.96         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 3.78/3.96          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33))
% 3.78/3.96          | ((k4_subset_1 @ X33 @ X32 @ X34) = (k2_xboole_0 @ X32 @ X34)))),
% 3.78/3.96      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 3.78/3.96  thf('84', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         (((k4_subset_1 @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)) @ sk_B @ X1)
% 3.78/3.96            = (k2_xboole_0 @ sk_B @ X1))
% 3.78/3.96          | ~ (m1_subset_1 @ X1 @ 
% 3.78/3.96               (k1_zfmisc_1 @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))))),
% 3.78/3.96      inference('sup-', [status(thm)], ['82', '83'])).
% 3.78/3.96  thf('85', plain,
% 3.78/3.96      ((((k4_subset_1 @ (k2_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B @ 
% 3.78/3.96          (k2_tops_1 @ sk_A @ sk_B))
% 3.78/3.96          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 3.78/3.96         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.78/3.96      inference('sup-', [status(thm)], ['79', '84'])).
% 3.78/3.96  thf('86', plain,
% 3.78/3.96      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 3.78/3.96      inference('sup-', [status(thm)], ['16', '17'])).
% 3.78/3.96  thf(t39_xboole_1, axiom,
% 3.78/3.96    (![A:$i,B:$i]:
% 3.78/3.96     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.78/3.96  thf('87', plain,
% 3.78/3.96      (![X10 : $i, X11 : $i]:
% 3.78/3.96         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 3.78/3.96           = (k2_xboole_0 @ X10 @ X11))),
% 3.78/3.96      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.78/3.96  thf('88', plain,
% 3.78/3.96      (((k2_xboole_0 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 3.78/3.96         = (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 3.78/3.96      inference('sup+', [status(thm)], ['86', '87'])).
% 3.78/3.96  thf('89', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.78/3.96      inference('sup+', [status(thm)], ['2', '3'])).
% 3.78/3.96  thf('90', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.78/3.96      inference('sup+', [status(thm)], ['2', '3'])).
% 3.78/3.96  thf('91', plain,
% 3.78/3.96      (((k2_xboole_0 @ k1_xboole_0 @ (u1_struct_0 @ sk_A))
% 3.78/3.96         = (k2_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 3.78/3.96      inference('demod', [status(thm)], ['88', '89', '90'])).
% 3.78/3.96  thf('92', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 3.78/3.96      inference('cnf', [status(esa)], [t3_boole])).
% 3.78/3.96  thf('93', plain,
% 3.78/3.96      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 3.78/3.96      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.78/3.96  thf('94', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 3.78/3.96      inference('sup+', [status(thm)], ['92', '93'])).
% 3.78/3.96  thf('95', plain,
% 3.78/3.96      (![X42 : $i, X44 : $i]:
% 3.78/3.96         ((m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X44)) | ~ (r1_tarski @ X42 @ X44))),
% 3.78/3.96      inference('cnf', [status(esa)], [t3_subset])).
% 3.78/3.96  thf('96', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.78/3.96      inference('sup-', [status(thm)], ['94', '95'])).
% 3.78/3.96  thf(d5_subset_1, axiom,
% 3.78/3.96    (![A:$i,B:$i]:
% 3.78/3.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.78/3.96       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 3.78/3.96  thf('97', plain,
% 3.78/3.96      (![X26 : $i, X27 : $i]:
% 3.78/3.96         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 3.78/3.96          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 3.78/3.96      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.78/3.96  thf('98', plain,
% 3.78/3.96      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 3.78/3.96      inference('sup-', [status(thm)], ['96', '97'])).
% 3.78/3.96  thf('99', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 3.78/3.96      inference('sup-', [status(thm)], ['41', '42'])).
% 3.78/3.96  thf('100', plain,
% 3.78/3.96      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 3.78/3.96      inference('sup+', [status(thm)], ['98', '99'])).
% 3.78/3.96  thf('101', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 3.78/3.96      inference('cnf', [status(esa)], [t3_boole])).
% 3.78/3.96  thf('102', plain,
% 3.78/3.96      (![X19 : $i, X20 : $i]:
% 3.78/3.96         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 3.78/3.96           = (k3_xboole_0 @ X19 @ X20))),
% 3.78/3.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.78/3.96  thf('103', plain,
% 3.78/3.96      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 3.78/3.96      inference('sup+', [status(thm)], ['101', '102'])).
% 3.78/3.96  thf('104', plain,
% 3.78/3.96      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 3.78/3.96      inference('sup-', [status(thm)], ['96', '97'])).
% 3.78/3.96  thf(t2_boole, axiom,
% 3.78/3.96    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 3.78/3.96  thf('105', plain,
% 3.78/3.96      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 3.78/3.96      inference('cnf', [status(esa)], [t2_boole])).
% 3.78/3.96  thf('106', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 3.78/3.96      inference('demod', [status(thm)], ['103', '104', '105'])).
% 3.78/3.96  thf('107', plain,
% 3.78/3.96      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.78/3.96      inference('demod', [status(thm)], ['100', '106'])).
% 3.78/3.96  thf('108', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.78/3.96      inference('sup-', [status(thm)], ['94', '95'])).
% 3.78/3.96  thf('109', plain,
% 3.78/3.96      (![X32 : $i, X33 : $i, X34 : $i]:
% 3.78/3.96         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 3.78/3.96          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33))
% 3.78/3.96          | ((k4_subset_1 @ X33 @ X32 @ X34) = (k2_xboole_0 @ X32 @ X34)))),
% 3.78/3.96      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 3.78/3.96  thf('110', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         (((k4_subset_1 @ X0 @ X0 @ X1) = (k2_xboole_0 @ X0 @ X1))
% 3.78/3.96          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 3.78/3.96      inference('sup-', [status(thm)], ['108', '109'])).
% 3.78/3.96  thf('111', plain,
% 3.78/3.96      (![X0 : $i]:
% 3.78/3.96         ((k4_subset_1 @ X0 @ X0 @ k1_xboole_0)
% 3.78/3.96           = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 3.78/3.96      inference('sup-', [status(thm)], ['107', '110'])).
% 3.78/3.96  thf('112', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.78/3.96      inference('sup-', [status(thm)], ['94', '95'])).
% 3.78/3.96  thf(t25_subset_1, axiom,
% 3.78/3.96    (![A:$i,B:$i]:
% 3.78/3.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.78/3.96       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 3.78/3.96         ( k2_subset_1 @ A ) ) ))).
% 3.78/3.96  thf('113', plain,
% 3.78/3.96      (![X38 : $i, X39 : $i]:
% 3.78/3.96         (((k4_subset_1 @ X38 @ X39 @ (k3_subset_1 @ X38 @ X39))
% 3.78/3.96            = (k2_subset_1 @ X38))
% 3.78/3.96          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 3.78/3.96      inference('cnf', [status(esa)], [t25_subset_1])).
% 3.78/3.96  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 3.78/3.96  thf('114', plain, (![X25 : $i]: ((k2_subset_1 @ X25) = (X25))),
% 3.78/3.96      inference('cnf', [status(esa)], [d4_subset_1])).
% 3.78/3.96  thf('115', plain,
% 3.78/3.96      (![X38 : $i, X39 : $i]:
% 3.78/3.96         (((k4_subset_1 @ X38 @ X39 @ (k3_subset_1 @ X38 @ X39)) = (X38))
% 3.78/3.96          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 3.78/3.96      inference('demod', [status(thm)], ['113', '114'])).
% 3.78/3.96  thf('116', plain,
% 3.78/3.96      (![X0 : $i]: ((k4_subset_1 @ X0 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 3.78/3.96      inference('sup-', [status(thm)], ['112', '115'])).
% 3.78/3.96  thf('117', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 3.78/3.96      inference('demod', [status(thm)], ['103', '104', '105'])).
% 3.78/3.96  thf('118', plain,
% 3.78/3.96      (![X0 : $i]: ((k4_subset_1 @ X0 @ X0 @ k1_xboole_0) = (X0))),
% 3.78/3.96      inference('demod', [status(thm)], ['116', '117'])).
% 3.78/3.96  thf('119', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 3.78/3.96      inference('demod', [status(thm)], ['111', '118'])).
% 3.78/3.96  thf('120', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.78/3.96      inference('sup+', [status(thm)], ['2', '3'])).
% 3.78/3.96  thf('121', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.78/3.96      inference('sup+', [status(thm)], ['119', '120'])).
% 3.78/3.96  thf('122', plain,
% 3.78/3.96      (((u1_struct_0 @ sk_A) = (k2_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 3.78/3.96      inference('demod', [status(thm)], ['91', '121'])).
% 3.78/3.96  thf('123', plain,
% 3.78/3.96      ((![X0 : $i]:
% 3.78/3.96          (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_xboole_0 @ X0 @ sk_B)))
% 3.78/3.96         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.78/3.96      inference('sup-', [status(thm)], ['74', '75'])).
% 3.78/3.96  thf('124', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.78/3.96      inference('sup+', [status(thm)], ['2', '3'])).
% 3.78/3.96  thf('125', plain,
% 3.78/3.96      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.78/3.96         ((r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 3.78/3.96          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 3.78/3.96      inference('cnf', [status(esa)], [t43_xboole_1])).
% 3.78/3.96  thf('126', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.78/3.96         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 3.78/3.96          | (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 3.78/3.96      inference('sup-', [status(thm)], ['124', '125'])).
% 3.78/3.96  thf('127', plain,
% 3.78/3.96      ((![X0 : $i]:
% 3.78/3.96          (r1_tarski @ (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ X0))
% 3.78/3.96         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.78/3.96      inference('sup-', [status(thm)], ['123', '126'])).
% 3.78/3.96  thf('128', plain,
% 3.78/3.96      (![X8 : $i, X9 : $i]:
% 3.78/3.96         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 3.78/3.96      inference('cnf', [status(esa)], [t38_xboole_1])).
% 3.78/3.96  thf('129', plain,
% 3.78/3.96      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 3.78/3.96         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.78/3.96      inference('sup-', [status(thm)], ['127', '128'])).
% 3.78/3.96  thf('130', plain,
% 3.78/3.96      (![X10 : $i, X11 : $i]:
% 3.78/3.96         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 3.78/3.96           = (k2_xboole_0 @ X10 @ X11))),
% 3.78/3.96      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.78/3.96  thf('131', plain,
% 3.78/3.96      ((((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 3.78/3.96          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 3.78/3.96         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.78/3.96      inference('sup+', [status(thm)], ['129', '130'])).
% 3.78/3.96  thf('132', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.78/3.96      inference('sup+', [status(thm)], ['2', '3'])).
% 3.78/3.96  thf('133', plain,
% 3.78/3.96      ((((k2_xboole_0 @ k1_xboole_0 @ sk_B)
% 3.78/3.96          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 3.78/3.96         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.78/3.96      inference('demod', [status(thm)], ['131', '132'])).
% 3.78/3.96  thf('134', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.78/3.96      inference('sup+', [status(thm)], ['119', '120'])).
% 3.78/3.96  thf('135', plain,
% 3.78/3.96      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 3.78/3.96         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.78/3.96      inference('demod', [status(thm)], ['133', '134'])).
% 3.78/3.96  thf('136', plain,
% 3.78/3.96      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 3.78/3.96          = (sk_B)))
% 3.78/3.96         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.78/3.96      inference('demod', [status(thm)], ['85', '122', '135'])).
% 3.78/3.96  thf('137', plain,
% 3.78/3.96      (((k2_pre_topc @ sk_A @ sk_B)
% 3.78/3.96         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96            (k2_tops_1 @ sk_A @ sk_B)))),
% 3.78/3.96      inference('demod', [status(thm)], ['52', '53'])).
% 3.78/3.96  thf('138', plain,
% 3.78/3.96      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 3.78/3.96         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.78/3.96      inference('sup+', [status(thm)], ['136', '137'])).
% 3.78/3.96  thf('139', plain,
% 3.78/3.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.78/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.78/3.96  thf(fc1_tops_1, axiom,
% 3.78/3.96    (![A:$i,B:$i]:
% 3.78/3.96     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 3.78/3.96         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 3.78/3.96       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 3.78/3.96  thf('140', plain,
% 3.78/3.96      (![X49 : $i, X50 : $i]:
% 3.78/3.96         (~ (l1_pre_topc @ X49)
% 3.78/3.96          | ~ (v2_pre_topc @ X49)
% 3.78/3.96          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 3.78/3.96          | (v4_pre_topc @ (k2_pre_topc @ X49 @ X50) @ X49))),
% 3.78/3.96      inference('cnf', [status(esa)], [fc1_tops_1])).
% 3.78/3.96  thf('141', plain,
% 3.78/3.96      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 3.78/3.96        | ~ (v2_pre_topc @ sk_A)
% 3.78/3.96        | ~ (l1_pre_topc @ sk_A))),
% 3.78/3.96      inference('sup-', [status(thm)], ['139', '140'])).
% 3.78/3.96  thf('142', plain, ((v2_pre_topc @ sk_A)),
% 3.78/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.78/3.96  thf('143', plain, ((l1_pre_topc @ sk_A)),
% 3.78/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.78/3.96  thf('144', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 3.78/3.96      inference('demod', [status(thm)], ['141', '142', '143'])).
% 3.78/3.96  thf('145', plain,
% 3.78/3.96      (((v4_pre_topc @ sk_B @ sk_A))
% 3.78/3.96         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.78/3.96      inference('sup+', [status(thm)], ['138', '144'])).
% 3.78/3.96  thf('146', plain,
% 3.78/3.96      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 3.78/3.96      inference('split', [status(esa)], ['63'])).
% 3.78/3.96  thf('147', plain,
% 3.78/3.96      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 3.78/3.96       ~
% 3.78/3.96       (((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96             (k1_tops_1 @ sk_A @ sk_B))))),
% 3.78/3.96      inference('sup-', [status(thm)], ['145', '146'])).
% 3.78/3.96  thf('148', plain,
% 3.78/3.96      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 3.78/3.96       (((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96             (k1_tops_1 @ sk_A @ sk_B))))),
% 3.78/3.96      inference('split', [status(esa)], ['55'])).
% 3.78/3.96  thf('149', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 3.78/3.96      inference('sat_resolution*', [status(thm)], ['64', '147', '148'])).
% 3.78/3.96  thf('150', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 3.78/3.96      inference('simpl_trail', [status(thm)], ['62', '149'])).
% 3.78/3.96  thf('151', plain,
% 3.78/3.96      (((sk_B)
% 3.78/3.96         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96            (k2_tops_1 @ sk_A @ sk_B)))),
% 3.78/3.96      inference('demod', [status(thm)], ['54', '150'])).
% 3.78/3.96  thf('152', plain,
% 3.78/3.96      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 3.78/3.96         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 3.78/3.96      inference('demod', [status(thm)], ['32', '33', '34'])).
% 3.78/3.96  thf('153', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.78/3.96      inference('sup+', [status(thm)], ['2', '3'])).
% 3.78/3.96  thf('154', plain,
% 3.78/3.96      (((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.78/3.96      inference('demod', [status(thm)], ['49', '151', '152', '153'])).
% 3.78/3.96  thf('155', plain,
% 3.78/3.96      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 3.78/3.96      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.78/3.96  thf('156', plain,
% 3.78/3.96      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.78/3.96         ((r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 3.78/3.96          | ~ (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18))),
% 3.78/3.96      inference('cnf', [status(esa)], [t44_xboole_1])).
% 3.78/3.96  thf('157', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 3.78/3.96      inference('sup-', [status(thm)], ['155', '156'])).
% 3.78/3.96  thf('158', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 3.78/3.96      inference('demod', [status(thm)], ['111', '118'])).
% 3.78/3.96  thf('159', plain,
% 3.78/3.96      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.78/3.96         ((r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 3.78/3.96          | ~ (r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 3.78/3.96      inference('cnf', [status(esa)], [t43_xboole_1])).
% 3.78/3.96  thf('160', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         (~ (r1_tarski @ X1 @ X0)
% 3.78/3.96          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 3.78/3.96      inference('sup-', [status(thm)], ['158', '159'])).
% 3.78/3.96  thf('161', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         (r1_tarski @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 3.78/3.96          k1_xboole_0)),
% 3.78/3.96      inference('sup-', [status(thm)], ['157', '160'])).
% 3.78/3.96  thf('162', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.78/3.96      inference('sup+', [status(thm)], ['25', '26'])).
% 3.78/3.96  thf('163', plain,
% 3.78/3.96      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 3.78/3.96      inference('cnf', [status(esa)], [t2_boole])).
% 3.78/3.96  thf('164', plain,
% 3.78/3.96      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.78/3.96      inference('sup+', [status(thm)], ['162', '163'])).
% 3.78/3.96  thf('165', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k4_xboole_0 @ X0 @ X1)
% 3.78/3.96           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 3.78/3.96      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.78/3.96  thf('166', plain,
% 3.78/3.96      (![X8 : $i, X9 : $i]:
% 3.78/3.96         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 3.78/3.96      inference('cnf', [status(esa)], [t38_xboole_1])).
% 3.78/3.96  thf('167', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         (~ (r1_tarski @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 3.78/3.96          | ((X0) = (k1_xboole_0)))),
% 3.78/3.96      inference('sup-', [status(thm)], ['165', '166'])).
% 3.78/3.96  thf('168', plain,
% 3.78/3.96      (![X0 : $i]:
% 3.78/3.96         (~ (r1_tarski @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 3.78/3.96          | ((X0) = (k1_xboole_0)))),
% 3.78/3.96      inference('sup-', [status(thm)], ['164', '167'])).
% 3.78/3.96  thf('169', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 3.78/3.96      inference('cnf', [status(esa)], [t3_boole])).
% 3.78/3.96  thf('170', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k4_xboole_0 @ X0 @ X1)
% 3.78/3.96           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 3.78/3.96      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.78/3.96  thf('171', plain,
% 3.78/3.96      (![X0 : $i]:
% 3.78/3.96         ((X0) = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 3.78/3.96      inference('sup+', [status(thm)], ['169', '170'])).
% 3.78/3.96  thf('172', plain,
% 3.78/3.96      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 3.78/3.96      inference('cnf', [status(esa)], [t2_boole])).
% 3.78/3.96  thf('173', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 3.78/3.96      inference('demod', [status(thm)], ['171', '172'])).
% 3.78/3.96  thf('174', plain,
% 3.78/3.96      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 3.78/3.96      inference('demod', [status(thm)], ['168', '173'])).
% 3.78/3.96  thf('175', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 3.78/3.96      inference('sup-', [status(thm)], ['161', '174'])).
% 3.78/3.96  thf('176', plain,
% 3.78/3.96      (((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0))),
% 3.78/3.96      inference('sup+', [status(thm)], ['154', '175'])).
% 3.78/3.96  thf('177', plain,
% 3.78/3.96      (![X19 : $i, X20 : $i]:
% 3.78/3.96         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 3.78/3.96           = (k3_xboole_0 @ X19 @ X20))),
% 3.78/3.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.78/3.96  thf('178', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.78/3.96      inference('sup+', [status(thm)], ['25', '26'])).
% 3.78/3.96  thf('179', plain,
% 3.78/3.96      (![X19 : $i, X20 : $i]:
% 3.78/3.96         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 3.78/3.96           = (k3_xboole_0 @ X19 @ X20))),
% 3.78/3.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.78/3.96  thf('180', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 3.78/3.96      inference('sup-', [status(thm)], ['41', '42'])).
% 3.78/3.96  thf('181', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 3.78/3.96      inference('sup+', [status(thm)], ['179', '180'])).
% 3.78/3.96  thf('182', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 3.78/3.96      inference('sup+', [status(thm)], ['178', '181'])).
% 3.78/3.96  thf(involutiveness_k3_subset_1, axiom,
% 3.78/3.96    (![A:$i,B:$i]:
% 3.78/3.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.78/3.96       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 3.78/3.96  thf('183', plain,
% 3.78/3.96      (![X30 : $i, X31 : $i]:
% 3.78/3.96         (((k3_subset_1 @ X31 @ (k3_subset_1 @ X31 @ X30)) = (X30))
% 3.78/3.96          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 3.78/3.96      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 3.78/3.96  thf('184', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 3.78/3.96           = (k3_xboole_0 @ X1 @ X0))),
% 3.78/3.96      inference('sup-', [status(thm)], ['182', '183'])).
% 3.78/3.96  thf('185', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.78/3.96      inference('sup+', [status(thm)], ['25', '26'])).
% 3.78/3.96  thf('186', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 3.78/3.96      inference('sup-', [status(thm)], ['41', '42'])).
% 3.78/3.96  thf('187', plain,
% 3.78/3.96      (![X30 : $i, X31 : $i]:
% 3.78/3.96         (((k3_subset_1 @ X31 @ (k3_subset_1 @ X31 @ X30)) = (X30))
% 3.78/3.96          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 3.78/3.96      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 3.78/3.96  thf('188', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 3.78/3.96           = (k4_xboole_0 @ X0 @ X1))),
% 3.78/3.96      inference('sup-', [status(thm)], ['186', '187'])).
% 3.78/3.96  thf('189', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 3.78/3.96      inference('sup-', [status(thm)], ['41', '42'])).
% 3.78/3.96  thf('190', plain,
% 3.78/3.96      (![X26 : $i, X27 : $i]:
% 3.78/3.96         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 3.78/3.96          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 3.78/3.96      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.78/3.96  thf('191', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 3.78/3.96           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 3.78/3.96      inference('sup-', [status(thm)], ['189', '190'])).
% 3.78/3.96  thf('192', plain,
% 3.78/3.96      (![X19 : $i, X20 : $i]:
% 3.78/3.96         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 3.78/3.96           = (k3_xboole_0 @ X19 @ X20))),
% 3.78/3.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.78/3.96  thf('193', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 3.78/3.96           = (k3_xboole_0 @ X1 @ X0))),
% 3.78/3.96      inference('sup+', [status(thm)], ['191', '192'])).
% 3.78/3.96  thf('194', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 3.78/3.96           = (k4_xboole_0 @ X0 @ X1))),
% 3.78/3.96      inference('demod', [status(thm)], ['188', '193'])).
% 3.78/3.96  thf('195', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 3.78/3.96           = (k4_xboole_0 @ X0 @ X1))),
% 3.78/3.96      inference('sup+', [status(thm)], ['185', '194'])).
% 3.78/3.96  thf('196', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 3.78/3.96           = (k3_xboole_0 @ X1 @ X0))),
% 3.78/3.96      inference('demod', [status(thm)], ['184', '195'])).
% 3.78/3.96  thf('197', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k3_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 3.78/3.96           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))),
% 3.78/3.96      inference('sup+', [status(thm)], ['177', '196'])).
% 3.78/3.96  thf('198', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 3.78/3.96           = (k4_xboole_0 @ X0 @ X1))),
% 3.78/3.96      inference('demod', [status(thm)], ['188', '193'])).
% 3.78/3.96  thf('199', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.78/3.96      inference('sup+', [status(thm)], ['25', '26'])).
% 3.78/3.96  thf('200', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k4_xboole_0 @ X1 @ X0)
% 3.78/3.96           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.78/3.96      inference('demod', [status(thm)], ['197', '198', '199'])).
% 3.78/3.96  thf('201', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 3.78/3.96           = (k4_xboole_0 @ X0 @ X1))),
% 3.78/3.96      inference('demod', [status(thm)], ['188', '193'])).
% 3.78/3.96  thf('202', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 3.78/3.96           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.78/3.96      inference('sup+', [status(thm)], ['200', '201'])).
% 3.78/3.96  thf('203', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 3.78/3.96           = (k3_xboole_0 @ X1 @ X0))),
% 3.78/3.96      inference('demod', [status(thm)], ['184', '195'])).
% 3.78/3.96  thf('204', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k3_xboole_0 @ X0 @ X1)
% 3.78/3.96           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.78/3.96      inference('demod', [status(thm)], ['202', '203'])).
% 3.78/3.96  thf('205', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.78/3.96      inference('sup-', [status(thm)], ['94', '95'])).
% 3.78/3.96  thf('206', plain,
% 3.78/3.96      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.78/3.96         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 3.78/3.96          | ((k7_subset_1 @ X36 @ X35 @ X37) = (k4_xboole_0 @ X35 @ X37)))),
% 3.78/3.96      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 3.78/3.96  thf('207', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 3.78/3.96      inference('sup-', [status(thm)], ['205', '206'])).
% 3.78/3.96  thf('208', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k7_subset_1 @ X0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 3.78/3.96           = (k3_xboole_0 @ X1 @ X0))),
% 3.78/3.96      inference('sup+', [status(thm)], ['204', '207'])).
% 3.78/3.96  thf('209', plain,
% 3.78/3.96      (((k7_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 3.78/3.96         k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.78/3.96      inference('sup+', [status(thm)], ['176', '208'])).
% 3.78/3.96  thf('210', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 3.78/3.96      inference('sup-', [status(thm)], ['205', '206'])).
% 3.78/3.96  thf('211', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 3.78/3.96      inference('cnf', [status(esa)], [t3_boole])).
% 3.78/3.96  thf('212', plain,
% 3.78/3.96      (![X0 : $i]: ((k7_subset_1 @ X0 @ X0 @ k1_xboole_0) = (X0))),
% 3.78/3.96      inference('sup+', [status(thm)], ['210', '211'])).
% 3.78/3.96  thf('213', plain,
% 3.78/3.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 3.78/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.78/3.96  thf(t74_tops_1, axiom,
% 3.78/3.96    (![A:$i]:
% 3.78/3.96     ( ( l1_pre_topc @ A ) =>
% 3.78/3.96       ( ![B:$i]:
% 3.78/3.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 3.78/3.96           ( ( k1_tops_1 @ A @ B ) =
% 3.78/3.96             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 3.78/3.96  thf('214', plain,
% 3.78/3.96      (![X55 : $i, X56 : $i]:
% 3.78/3.96         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 3.78/3.96          | ((k1_tops_1 @ X56 @ X55)
% 3.78/3.96              = (k7_subset_1 @ (u1_struct_0 @ X56) @ X55 @ 
% 3.78/3.96                 (k2_tops_1 @ X56 @ X55)))
% 3.78/3.96          | ~ (l1_pre_topc @ X56))),
% 3.78/3.96      inference('cnf', [status(esa)], [t74_tops_1])).
% 3.78/3.96  thf('215', plain,
% 3.78/3.96      ((~ (l1_pre_topc @ sk_A)
% 3.78/3.96        | ((k1_tops_1 @ sk_A @ sk_B)
% 3.78/3.96            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96               (k2_tops_1 @ sk_A @ sk_B))))),
% 3.78/3.96      inference('sup-', [status(thm)], ['213', '214'])).
% 3.78/3.96  thf('216', plain, ((l1_pre_topc @ sk_A)),
% 3.78/3.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.78/3.96  thf('217', plain,
% 3.78/3.96      (![X0 : $i]:
% 3.78/3.96         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 3.78/3.96           = (k4_xboole_0 @ sk_B @ X0))),
% 3.78/3.96      inference('sup-', [status(thm)], ['66', '67'])).
% 3.78/3.96  thf('218', plain,
% 3.78/3.96      (((k1_tops_1 @ sk_A @ sk_B)
% 3.78/3.96         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.78/3.96      inference('demod', [status(thm)], ['215', '216', '217'])).
% 3.78/3.96  thf('219', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k4_xboole_0 @ X0 @ X1)
% 3.78/3.96           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 3.78/3.96      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.78/3.96  thf('220', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k3_xboole_0 @ X0 @ X1)
% 3.78/3.96           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.78/3.96      inference('demod', [status(thm)], ['202', '203'])).
% 3.78/3.96  thf('221', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k3_xboole_0 @ X0 @ X1)
% 3.78/3.96           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 3.78/3.96      inference('sup+', [status(thm)], ['219', '220'])).
% 3.78/3.96  thf('222', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k4_xboole_0 @ X1 @ X0)
% 3.78/3.96           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.78/3.96      inference('demod', [status(thm)], ['197', '198', '199'])).
% 3.78/3.96  thf('223', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]:
% 3.78/3.96         ((k3_xboole_0 @ X0 @ X1)
% 3.78/3.96           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.78/3.96      inference('demod', [status(thm)], ['221', '222'])).
% 3.78/3.96  thf('224', plain,
% 3.78/3.96      (((k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)
% 3.78/3.96         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 3.78/3.96      inference('sup+', [status(thm)], ['218', '223'])).
% 3.78/3.96  thf('225', plain,
% 3.78/3.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.78/3.96      inference('sup+', [status(thm)], ['25', '26'])).
% 3.78/3.96  thf('226', plain,
% 3.78/3.96      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 3.78/3.96         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 3.78/3.96      inference('demod', [status(thm)], ['224', '225'])).
% 3.78/3.96  thf('227', plain,
% 3.78/3.96      (((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 3.78/3.96      inference('demod', [status(thm)], ['209', '212', '226'])).
% 3.78/3.96  thf('228', plain,
% 3.78/3.96      (((k1_tops_1 @ sk_A @ sk_B)
% 3.78/3.96         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.78/3.96      inference('demod', [status(thm)], ['215', '216', '217'])).
% 3.78/3.96  thf('229', plain,
% 3.78/3.96      (![X19 : $i, X20 : $i]:
% 3.78/3.96         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 3.78/3.96           = (k3_xboole_0 @ X19 @ X20))),
% 3.78/3.96      inference('cnf', [status(esa)], [t48_xboole_1])).
% 3.78/3.96  thf('230', plain,
% 3.78/3.96      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 3.78/3.96         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 3.78/3.96      inference('sup+', [status(thm)], ['228', '229'])).
% 3.78/3.96  thf('231', plain,
% 3.78/3.96      (![X0 : $i]:
% 3.78/3.96         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 3.78/3.96           = (k4_xboole_0 @ sk_B @ X0))),
% 3.78/3.96      inference('sup-', [status(thm)], ['66', '67'])).
% 3.78/3.96  thf('232', plain,
% 3.78/3.96      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96              (k1_tops_1 @ sk_A @ sk_B))))
% 3.78/3.96         <= (~
% 3.78/3.96             (((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.78/3.96      inference('split', [status(esa)], ['63'])).
% 3.78/3.96  thf('233', plain,
% 3.78/3.96      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 3.78/3.96         <= (~
% 3.78/3.96             (((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.78/3.96      inference('sup-', [status(thm)], ['231', '232'])).
% 3.78/3.96  thf('234', plain,
% 3.78/3.96      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96          != (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 3.78/3.96         <= (~
% 3.78/3.96             (((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.78/3.96      inference('sup-', [status(thm)], ['230', '233'])).
% 3.78/3.96  thf('235', plain,
% 3.78/3.96      (((k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 3.78/3.96         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 3.78/3.96      inference('demod', [status(thm)], ['224', '225'])).
% 3.78/3.96  thf('236', plain,
% 3.78/3.96      ((((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96          != (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 3.78/3.96         <= (~
% 3.78/3.96             (((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 3.78/3.96      inference('demod', [status(thm)], ['234', '235'])).
% 3.78/3.96  thf('237', plain,
% 3.78/3.96      (~
% 3.78/3.96       (((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 3.78/3.96             (k1_tops_1 @ sk_A @ sk_B))))),
% 3.78/3.96      inference('sat_resolution*', [status(thm)], ['64', '147'])).
% 3.78/3.96  thf('238', plain,
% 3.78/3.96      (((k2_tops_1 @ sk_A @ sk_B)
% 3.78/3.96         != (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 3.78/3.96      inference('simpl_trail', [status(thm)], ['236', '237'])).
% 3.78/3.96  thf('239', plain, ($false),
% 3.78/3.96      inference('simplify_reflect-', [status(thm)], ['227', '238'])).
% 3.78/3.96  
% 3.78/3.96  % SZS output end Refutation
% 3.78/3.96  
% 3.78/3.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
