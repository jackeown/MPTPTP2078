%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vZnu1cAvIR

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:03 EST 2020

% Result     : Theorem 6.64s
% Output     : Refutation 6.64s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 139 expanded)
%              Number of leaves         :   23 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :  678 (1612 expanded)
%              Number of equality atoms :    7 (  14 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t50_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k1_tops_1 @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( r1_tarski @ ( k1_tops_1 @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k7_subset_1 @ X17 @ X16 @ X18 )
        = ( k4_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X23 @ X22 ) @ X22 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['10','11'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X19: $i,X21: $i] :
      ( ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( ( k7_subset_1 @ X17 @ X16 @ X18 )
        = ( k4_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X19: $i,X21: $i] :
      ( ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( r1_tarski @ X24 @ X26 )
      | ( r1_tarski @ ( k1_tops_1 @ X25 @ X24 ) @ ( k1_tops_1 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('40',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X23 @ X22 ) @ X22 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X3 @ X5 )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X23 @ X22 ) @ X22 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t64_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D )
        & ( r1_xboole_0 @ B @ D ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('52',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ~ ( r1_tarski @ X10 @ X12 )
      | ~ ( r1_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t64_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r1_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['45','54'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('56',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ X15 )
      | ( r1_tarski @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['20','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vZnu1cAvIR
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:44:55 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 6.64/6.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.64/6.85  % Solved by: fo/fo7.sh
% 6.64/6.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.64/6.85  % done 8152 iterations in 6.388s
% 6.64/6.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.64/6.85  % SZS output start Refutation
% 6.64/6.85  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 6.64/6.85  thf(sk_C_type, type, sk_C: $i).
% 6.64/6.85  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.64/6.85  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 6.64/6.85  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 6.64/6.85  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 6.64/6.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.64/6.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.64/6.85  thf(sk_A_type, type, sk_A: $i).
% 6.64/6.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.64/6.85  thf(sk_B_type, type, sk_B: $i).
% 6.64/6.85  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 6.64/6.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.64/6.85  thf(t50_tops_1, conjecture,
% 6.64/6.85    (![A:$i]:
% 6.64/6.85     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.64/6.85       ( ![B:$i]:
% 6.64/6.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.64/6.85           ( ![C:$i]:
% 6.64/6.85             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.64/6.85               ( r1_tarski @
% 6.64/6.85                 ( k1_tops_1 @
% 6.64/6.85                   A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 6.64/6.85                 ( k7_subset_1 @
% 6.64/6.85                   ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 6.64/6.85                   ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 6.64/6.85  thf(zf_stmt_0, negated_conjecture,
% 6.64/6.85    (~( ![A:$i]:
% 6.64/6.85        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.64/6.85          ( ![B:$i]:
% 6.64/6.85            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.64/6.85              ( ![C:$i]:
% 6.64/6.85                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.64/6.85                  ( r1_tarski @
% 6.64/6.85                    ( k1_tops_1 @
% 6.64/6.85                      A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 6.64/6.85                    ( k7_subset_1 @
% 6.64/6.85                      ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 6.64/6.85                      ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 6.64/6.85    inference('cnf.neg', [status(esa)], [t50_tops_1])).
% 6.64/6.85  thf('0', plain,
% 6.64/6.85      (~ (r1_tarski @ 
% 6.64/6.85          (k1_tops_1 @ sk_A @ 
% 6.64/6.85           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 6.64/6.85          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 6.64/6.85           (k1_tops_1 @ sk_A @ sk_C)))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf('1', plain,
% 6.64/6.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf(redefinition_k7_subset_1, axiom,
% 6.64/6.85    (![A:$i,B:$i,C:$i]:
% 6.64/6.85     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.64/6.85       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 6.64/6.85  thf('2', plain,
% 6.64/6.85      (![X16 : $i, X17 : $i, X18 : $i]:
% 6.64/6.85         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 6.64/6.85          | ((k7_subset_1 @ X17 @ X16 @ X18) = (k4_xboole_0 @ X16 @ X18)))),
% 6.64/6.85      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 6.64/6.85  thf('3', plain,
% 6.64/6.85      (![X0 : $i]:
% 6.64/6.85         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 6.64/6.85           = (k4_xboole_0 @ sk_B @ X0))),
% 6.64/6.85      inference('sup-', [status(thm)], ['1', '2'])).
% 6.64/6.85  thf('4', plain,
% 6.64/6.85      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 6.64/6.85          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 6.64/6.85           (k1_tops_1 @ sk_A @ sk_C)))),
% 6.64/6.85      inference('demod', [status(thm)], ['0', '3'])).
% 6.64/6.85  thf('5', plain,
% 6.64/6.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf(t3_subset, axiom,
% 6.64/6.85    (![A:$i,B:$i]:
% 6.64/6.85     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 6.64/6.85  thf('6', plain,
% 6.64/6.85      (![X19 : $i, X20 : $i]:
% 6.64/6.85         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 6.64/6.85      inference('cnf', [status(esa)], [t3_subset])).
% 6.64/6.85  thf('7', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 6.64/6.85      inference('sup-', [status(thm)], ['5', '6'])).
% 6.64/6.85  thf('8', plain,
% 6.64/6.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf(t44_tops_1, axiom,
% 6.64/6.85    (![A:$i]:
% 6.64/6.85     ( ( l1_pre_topc @ A ) =>
% 6.64/6.85       ( ![B:$i]:
% 6.64/6.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.64/6.85           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 6.64/6.85  thf('9', plain,
% 6.64/6.85      (![X22 : $i, X23 : $i]:
% 6.64/6.85         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 6.64/6.85          | (r1_tarski @ (k1_tops_1 @ X23 @ X22) @ X22)
% 6.64/6.85          | ~ (l1_pre_topc @ X23))),
% 6.64/6.85      inference('cnf', [status(esa)], [t44_tops_1])).
% 6.64/6.85  thf('10', plain,
% 6.64/6.85      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 6.64/6.85      inference('sup-', [status(thm)], ['8', '9'])).
% 6.64/6.85  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf('12', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 6.64/6.85      inference('demod', [status(thm)], ['10', '11'])).
% 6.64/6.85  thf(t1_xboole_1, axiom,
% 6.64/6.85    (![A:$i,B:$i,C:$i]:
% 6.64/6.85     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 6.64/6.85       ( r1_tarski @ A @ C ) ))).
% 6.64/6.85  thf('13', plain,
% 6.64/6.85      (![X6 : $i, X7 : $i, X8 : $i]:
% 6.64/6.85         (~ (r1_tarski @ X6 @ X7)
% 6.64/6.85          | ~ (r1_tarski @ X7 @ X8)
% 6.64/6.85          | (r1_tarski @ X6 @ X8))),
% 6.64/6.85      inference('cnf', [status(esa)], [t1_xboole_1])).
% 6.64/6.85  thf('14', plain,
% 6.64/6.85      (![X0 : $i]:
% 6.64/6.85         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 6.64/6.85          | ~ (r1_tarski @ sk_B @ X0))),
% 6.64/6.85      inference('sup-', [status(thm)], ['12', '13'])).
% 6.64/6.85  thf('15', plain,
% 6.64/6.85      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 6.64/6.85      inference('sup-', [status(thm)], ['7', '14'])).
% 6.64/6.85  thf('16', plain,
% 6.64/6.85      (![X19 : $i, X21 : $i]:
% 6.64/6.85         ((m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X19 @ X21))),
% 6.64/6.85      inference('cnf', [status(esa)], [t3_subset])).
% 6.64/6.85  thf('17', plain,
% 6.64/6.85      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 6.64/6.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.64/6.85      inference('sup-', [status(thm)], ['15', '16'])).
% 6.64/6.85  thf('18', plain,
% 6.64/6.85      (![X16 : $i, X17 : $i, X18 : $i]:
% 6.64/6.85         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 6.64/6.85          | ((k7_subset_1 @ X17 @ X16 @ X18) = (k4_xboole_0 @ X16 @ X18)))),
% 6.64/6.85      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 6.64/6.85  thf('19', plain,
% 6.64/6.85      (![X0 : $i]:
% 6.64/6.85         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 6.64/6.85           = (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 6.64/6.85      inference('sup-', [status(thm)], ['17', '18'])).
% 6.64/6.85  thf('20', plain,
% 6.64/6.85      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 6.64/6.85          (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 6.64/6.85      inference('demod', [status(thm)], ['4', '19'])).
% 6.64/6.85  thf('21', plain,
% 6.64/6.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf('22', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 6.64/6.85      inference('sup-', [status(thm)], ['5', '6'])).
% 6.64/6.85  thf(d10_xboole_0, axiom,
% 6.64/6.85    (![A:$i,B:$i]:
% 6.64/6.85     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.64/6.85  thf('23', plain,
% 6.64/6.85      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 6.64/6.85      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.64/6.85  thf('24', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 6.64/6.85      inference('simplify', [status(thm)], ['23'])).
% 6.64/6.85  thf(t106_xboole_1, axiom,
% 6.64/6.85    (![A:$i,B:$i,C:$i]:
% 6.64/6.85     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 6.64/6.85       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 6.64/6.85  thf('25', plain,
% 6.64/6.85      (![X3 : $i, X4 : $i, X5 : $i]:
% 6.64/6.85         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ X4 @ X5)))),
% 6.64/6.85      inference('cnf', [status(esa)], [t106_xboole_1])).
% 6.64/6.85  thf('26', plain,
% 6.64/6.85      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 6.64/6.85      inference('sup-', [status(thm)], ['24', '25'])).
% 6.64/6.85  thf('27', plain,
% 6.64/6.85      (![X6 : $i, X7 : $i, X8 : $i]:
% 6.64/6.85         (~ (r1_tarski @ X6 @ X7)
% 6.64/6.85          | ~ (r1_tarski @ X7 @ X8)
% 6.64/6.85          | (r1_tarski @ X6 @ X8))),
% 6.64/6.85      inference('cnf', [status(esa)], [t1_xboole_1])).
% 6.64/6.85  thf('28', plain,
% 6.64/6.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.64/6.85         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 6.64/6.85      inference('sup-', [status(thm)], ['26', '27'])).
% 6.64/6.85  thf('29', plain,
% 6.64/6.85      (![X0 : $i]:
% 6.64/6.85         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 6.64/6.85      inference('sup-', [status(thm)], ['22', '28'])).
% 6.64/6.85  thf('30', plain,
% 6.64/6.85      (![X19 : $i, X21 : $i]:
% 6.64/6.85         ((m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X19 @ X21))),
% 6.64/6.85      inference('cnf', [status(esa)], [t3_subset])).
% 6.64/6.85  thf('31', plain,
% 6.64/6.85      (![X0 : $i]:
% 6.64/6.85         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 6.64/6.85          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.64/6.85      inference('sup-', [status(thm)], ['29', '30'])).
% 6.64/6.85  thf(t48_tops_1, axiom,
% 6.64/6.85    (![A:$i]:
% 6.64/6.85     ( ( l1_pre_topc @ A ) =>
% 6.64/6.85       ( ![B:$i]:
% 6.64/6.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.64/6.85           ( ![C:$i]:
% 6.64/6.85             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.64/6.85               ( ( r1_tarski @ B @ C ) =>
% 6.64/6.85                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 6.64/6.85  thf('32', plain,
% 6.64/6.85      (![X24 : $i, X25 : $i, X26 : $i]:
% 6.64/6.85         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 6.64/6.85          | ~ (r1_tarski @ X24 @ X26)
% 6.64/6.85          | (r1_tarski @ (k1_tops_1 @ X25 @ X24) @ (k1_tops_1 @ X25 @ X26))
% 6.64/6.85          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 6.64/6.85          | ~ (l1_pre_topc @ X25))),
% 6.64/6.85      inference('cnf', [status(esa)], [t48_tops_1])).
% 6.64/6.85  thf('33', plain,
% 6.64/6.85      (![X0 : $i, X1 : $i]:
% 6.64/6.85         (~ (l1_pre_topc @ sk_A)
% 6.64/6.85          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.64/6.85          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 6.64/6.85             (k1_tops_1 @ sk_A @ X1))
% 6.64/6.85          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 6.64/6.85      inference('sup-', [status(thm)], ['31', '32'])).
% 6.64/6.85  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf('35', plain,
% 6.64/6.85      (![X0 : $i, X1 : $i]:
% 6.64/6.85         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 6.64/6.85          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 6.64/6.85             (k1_tops_1 @ sk_A @ X1))
% 6.64/6.85          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 6.64/6.85      inference('demod', [status(thm)], ['33', '34'])).
% 6.64/6.85  thf('36', plain,
% 6.64/6.85      (![X0 : $i]:
% 6.64/6.85         (~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_B)
% 6.64/6.85          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 6.64/6.85             (k1_tops_1 @ sk_A @ sk_B)))),
% 6.64/6.85      inference('sup-', [status(thm)], ['21', '35'])).
% 6.64/6.85  thf('37', plain,
% 6.64/6.85      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 6.64/6.85      inference('sup-', [status(thm)], ['24', '25'])).
% 6.64/6.85  thf('38', plain,
% 6.64/6.85      (![X0 : $i]:
% 6.64/6.85         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 6.64/6.85          (k1_tops_1 @ sk_A @ sk_B))),
% 6.64/6.85      inference('demod', [status(thm)], ['36', '37'])).
% 6.64/6.85  thf('39', plain,
% 6.64/6.85      (![X0 : $i]:
% 6.64/6.85         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 6.64/6.85          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.64/6.85      inference('sup-', [status(thm)], ['29', '30'])).
% 6.64/6.85  thf('40', plain,
% 6.64/6.85      (![X22 : $i, X23 : $i]:
% 6.64/6.85         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 6.64/6.85          | (r1_tarski @ (k1_tops_1 @ X23 @ X22) @ X22)
% 6.64/6.85          | ~ (l1_pre_topc @ X23))),
% 6.64/6.85      inference('cnf', [status(esa)], [t44_tops_1])).
% 6.64/6.85  thf('41', plain,
% 6.64/6.85      (![X0 : $i]:
% 6.64/6.85         (~ (l1_pre_topc @ sk_A)
% 6.64/6.85          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 6.64/6.85             (k4_xboole_0 @ sk_B @ X0)))),
% 6.64/6.85      inference('sup-', [status(thm)], ['39', '40'])).
% 6.64/6.85  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf('43', plain,
% 6.64/6.85      (![X0 : $i]:
% 6.64/6.85         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 6.64/6.85          (k4_xboole_0 @ sk_B @ X0))),
% 6.64/6.85      inference('demod', [status(thm)], ['41', '42'])).
% 6.64/6.85  thf('44', plain,
% 6.64/6.85      (![X3 : $i, X4 : $i, X5 : $i]:
% 6.64/6.85         ((r1_xboole_0 @ X3 @ X5)
% 6.64/6.85          | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ X4 @ X5)))),
% 6.64/6.85      inference('cnf', [status(esa)], [t106_xboole_1])).
% 6.64/6.85  thf('45', plain,
% 6.64/6.85      (![X0 : $i]:
% 6.64/6.85         (r1_xboole_0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ X0)),
% 6.64/6.85      inference('sup-', [status(thm)], ['43', '44'])).
% 6.64/6.85  thf('46', plain,
% 6.64/6.85      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf('47', plain,
% 6.64/6.85      (![X22 : $i, X23 : $i]:
% 6.64/6.85         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 6.64/6.85          | (r1_tarski @ (k1_tops_1 @ X23 @ X22) @ X22)
% 6.64/6.85          | ~ (l1_pre_topc @ X23))),
% 6.64/6.85      inference('cnf', [status(esa)], [t44_tops_1])).
% 6.64/6.85  thf('48', plain,
% 6.64/6.85      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 6.64/6.85      inference('sup-', [status(thm)], ['46', '47'])).
% 6.64/6.85  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 6.64/6.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.64/6.85  thf('50', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 6.64/6.85      inference('demod', [status(thm)], ['48', '49'])).
% 6.64/6.85  thf('51', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 6.64/6.85      inference('simplify', [status(thm)], ['23'])).
% 6.64/6.85  thf(t64_xboole_1, axiom,
% 6.64/6.85    (![A:$i,B:$i,C:$i,D:$i]:
% 6.64/6.85     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 6.64/6.85         ( r1_xboole_0 @ B @ D ) ) =>
% 6.64/6.85       ( r1_xboole_0 @ A @ C ) ))).
% 6.64/6.85  thf('52', plain,
% 6.64/6.85      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 6.64/6.85         ((r1_xboole_0 @ X9 @ X10)
% 6.64/6.85          | ~ (r1_tarski @ X9 @ X11)
% 6.64/6.85          | ~ (r1_tarski @ X10 @ X12)
% 6.64/6.85          | ~ (r1_xboole_0 @ X11 @ X12))),
% 6.64/6.85      inference('cnf', [status(esa)], [t64_xboole_1])).
% 6.64/6.85  thf('53', plain,
% 6.64/6.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.64/6.85         (~ (r1_xboole_0 @ X0 @ X1)
% 6.64/6.85          | ~ (r1_tarski @ X2 @ X1)
% 6.64/6.85          | (r1_xboole_0 @ X0 @ X2))),
% 6.64/6.85      inference('sup-', [status(thm)], ['51', '52'])).
% 6.64/6.85  thf('54', plain,
% 6.64/6.85      (![X0 : $i]:
% 6.64/6.85         ((r1_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 6.64/6.85          | ~ (r1_xboole_0 @ X0 @ sk_C))),
% 6.64/6.85      inference('sup-', [status(thm)], ['50', '53'])).
% 6.64/6.85  thf('55', plain,
% 6.64/6.85      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 6.64/6.85        (k1_tops_1 @ sk_A @ sk_C))),
% 6.64/6.85      inference('sup-', [status(thm)], ['45', '54'])).
% 6.64/6.85  thf(t86_xboole_1, axiom,
% 6.64/6.85    (![A:$i,B:$i,C:$i]:
% 6.64/6.85     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 6.64/6.85       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 6.64/6.85  thf('56', plain,
% 6.64/6.85      (![X13 : $i, X14 : $i, X15 : $i]:
% 6.64/6.85         (~ (r1_tarski @ X13 @ X14)
% 6.64/6.85          | ~ (r1_xboole_0 @ X13 @ X15)
% 6.64/6.85          | (r1_tarski @ X13 @ (k4_xboole_0 @ X14 @ X15)))),
% 6.64/6.85      inference('cnf', [status(esa)], [t86_xboole_1])).
% 6.64/6.85  thf('57', plain,
% 6.64/6.85      (![X0 : $i]:
% 6.64/6.85         ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 6.64/6.85           (k4_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))
% 6.64/6.85          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 6.64/6.85               X0))),
% 6.64/6.85      inference('sup-', [status(thm)], ['55', '56'])).
% 6.64/6.85  thf('58', plain,
% 6.64/6.85      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 6.64/6.85        (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 6.64/6.85      inference('sup-', [status(thm)], ['38', '57'])).
% 6.64/6.85  thf('59', plain, ($false), inference('demod', [status(thm)], ['20', '58'])).
% 6.64/6.85  
% 6.64/6.85  % SZS output end Refutation
% 6.64/6.85  
% 6.64/6.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
