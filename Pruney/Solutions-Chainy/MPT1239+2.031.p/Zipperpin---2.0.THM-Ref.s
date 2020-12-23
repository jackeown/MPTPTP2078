%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9qAaVS10Hb

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:04 EST 2020

% Result     : Theorem 26.31s
% Output     : Refutation 26.31s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 430 expanded)
%              Number of leaves         :   27 ( 148 expanded)
%              Depth                    :   20
%              Number of atoms          : 1226 (4468 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   18 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( ( k7_subset_1 @ X25 @ X24 @ X26 )
        = ( k4_xboole_0 @ X24 @ X26 ) ) ) ),
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

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( ( k7_subset_1 @ X25 @ X24 @ X26 )
        = ( k4_xboole_0 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X22 @ X21 @ X23 ) @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( r1_tarski @ X31 @ X33 )
      | ( r1_tarski @ ( k1_tops_1 @ X32 @ X31 ) @ ( k1_tops_1 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','22'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('27',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X30 @ X29 ) @ X29 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('32',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_xboole_0 @ X15 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ X20 )
      | ( r1_tarski @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ sk_C ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('38',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_xboole_0 @ X15 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('42',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ X20 )
      | ( r1_tarski @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X2 ) @ ( k4_xboole_0 @ X3 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X0 @ X2 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf(t64_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D )
        & ( r1_xboole_0 @ B @ D ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('45',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_tarski @ X11 @ X13 )
      | ~ ( r1_tarski @ X12 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t64_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ~ ( r1_tarski @ X4 @ X3 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X4 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X4 ) @ X3 )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ X1 ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('51',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('54',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_xboole_0 @ X15 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ X20 )
      | ( r1_tarski @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ ( k4_xboole_0 @ X3 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( r1_tarski @ X0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ ( k4_xboole_0 @ X3 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( r1_tarski @ X0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r1_tarski @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X3 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) @ ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X4 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('62',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X2 @ X3 ) @ X4 )
      | ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('65',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_xboole_0 @ X15 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) @ ( k4_xboole_0 @ X3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ X20 )
      | ( r1_tarski @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ X3 ) @ X2 ) @ ( k4_xboole_0 @ X4 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ X3 ) @ X2 ) @ X4 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X3 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X4 ) @ X3 )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X4 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ X3 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X3 )
      | ~ ( r1_tarski @ X4 @ X3 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X4 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X3 @ X2 ) @ X6 ) @ X5 )
      | ~ ( r1_tarski @ X5 @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X5: $i,X6: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X6 @ X0 ) @ X5 ) @ X0 ) ),
    inference('sup-',[status(thm)],['60','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X3 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('76',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 )
      | ( r1_xboole_0 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X2 @ X0 ) @ X3 ) @ X2 ) @ X4 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X4 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X3: $i,X4: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X4 ) @ X3 ) @ X0 ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( r1_tarski @ X0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X3 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) @ ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X4 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('80',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 )
      | ( r1_xboole_0 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X0 @ X6 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X5 @ X0 ) @ ( k4_xboole_0 @ X4 @ ( k2_xboole_0 @ X3 @ X0 ) ) ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) @ X6 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ X20 )
      | ( r1_tarski @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 )
      | ( r1_xboole_0 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('92',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X30 @ X29 ) @ X29 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 )
      | ( r1_xboole_0 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ X1 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['90','97'])).

thf('99',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ X20 )
      | ( r1_tarski @ X18 @ ( k4_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','100'])).

thf('102',plain,(
    $false ),
    inference(demod,[status(thm)],['12','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9qAaVS10Hb
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 26.31/26.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 26.31/26.53  % Solved by: fo/fo7.sh
% 26.31/26.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 26.31/26.53  % done 12305 iterations in 26.074s
% 26.31/26.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 26.31/26.53  % SZS output start Refutation
% 26.31/26.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 26.31/26.53  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 26.31/26.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 26.31/26.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 26.31/26.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 26.31/26.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 26.31/26.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 26.31/26.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 26.31/26.53  thf(sk_C_type, type, sk_C: $i).
% 26.31/26.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 26.31/26.53  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 26.31/26.53  thf(sk_A_type, type, sk_A: $i).
% 26.31/26.53  thf(sk_B_type, type, sk_B: $i).
% 26.31/26.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 26.31/26.53  thf(t50_tops_1, conjecture,
% 26.31/26.53    (![A:$i]:
% 26.31/26.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 26.31/26.53       ( ![B:$i]:
% 26.31/26.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 26.31/26.53           ( ![C:$i]:
% 26.31/26.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 26.31/26.53               ( r1_tarski @
% 26.31/26.53                 ( k1_tops_1 @
% 26.31/26.53                   A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 26.31/26.53                 ( k7_subset_1 @
% 26.31/26.53                   ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 26.31/26.53                   ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 26.31/26.53  thf(zf_stmt_0, negated_conjecture,
% 26.31/26.53    (~( ![A:$i]:
% 26.31/26.53        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 26.31/26.53          ( ![B:$i]:
% 26.31/26.53            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 26.31/26.53              ( ![C:$i]:
% 26.31/26.53                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 26.31/26.53                  ( r1_tarski @
% 26.31/26.53                    ( k1_tops_1 @
% 26.31/26.53                      A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 26.31/26.53                    ( k7_subset_1 @
% 26.31/26.53                      ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 26.31/26.53                      ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 26.31/26.53    inference('cnf.neg', [status(esa)], [t50_tops_1])).
% 26.31/26.53  thf('0', plain,
% 26.31/26.53      (~ (r1_tarski @ 
% 26.31/26.53          (k1_tops_1 @ sk_A @ 
% 26.31/26.53           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 26.31/26.53          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 26.31/26.53           (k1_tops_1 @ sk_A @ sk_C)))),
% 26.31/26.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.31/26.53  thf('1', plain,
% 26.31/26.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 26.31/26.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.31/26.53  thf(redefinition_k7_subset_1, axiom,
% 26.31/26.53    (![A:$i,B:$i,C:$i]:
% 26.31/26.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 26.31/26.53       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 26.31/26.53  thf('2', plain,
% 26.31/26.53      (![X24 : $i, X25 : $i, X26 : $i]:
% 26.31/26.53         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 26.31/26.53          | ((k7_subset_1 @ X25 @ X24 @ X26) = (k4_xboole_0 @ X24 @ X26)))),
% 26.31/26.53      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 26.31/26.53  thf('3', plain,
% 26.31/26.53      (![X0 : $i]:
% 26.31/26.53         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 26.31/26.53           = (k4_xboole_0 @ sk_B @ X0))),
% 26.31/26.53      inference('sup-', [status(thm)], ['1', '2'])).
% 26.31/26.53  thf('4', plain,
% 26.31/26.53      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 26.31/26.53          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 26.31/26.53           (k1_tops_1 @ sk_A @ sk_C)))),
% 26.31/26.53      inference('demod', [status(thm)], ['0', '3'])).
% 26.31/26.53  thf('5', plain,
% 26.31/26.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 26.31/26.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.31/26.53  thf(dt_k1_tops_1, axiom,
% 26.31/26.53    (![A:$i,B:$i]:
% 26.31/26.53     ( ( ( l1_pre_topc @ A ) & 
% 26.31/26.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 26.31/26.53       ( m1_subset_1 @
% 26.31/26.53         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 26.31/26.53  thf('6', plain,
% 26.31/26.53      (![X27 : $i, X28 : $i]:
% 26.31/26.53         (~ (l1_pre_topc @ X27)
% 26.31/26.53          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 26.31/26.53          | (m1_subset_1 @ (k1_tops_1 @ X27 @ X28) @ 
% 26.31/26.53             (k1_zfmisc_1 @ (u1_struct_0 @ X27))))),
% 26.31/26.53      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 26.31/26.53  thf('7', plain,
% 26.31/26.53      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 26.31/26.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 26.31/26.53        | ~ (l1_pre_topc @ sk_A))),
% 26.31/26.53      inference('sup-', [status(thm)], ['5', '6'])).
% 26.31/26.53  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 26.31/26.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.31/26.53  thf('9', plain,
% 26.31/26.53      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 26.31/26.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 26.31/26.53      inference('demod', [status(thm)], ['7', '8'])).
% 26.31/26.53  thf('10', plain,
% 26.31/26.53      (![X24 : $i, X25 : $i, X26 : $i]:
% 26.31/26.53         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 26.31/26.53          | ((k7_subset_1 @ X25 @ X24 @ X26) = (k4_xboole_0 @ X24 @ X26)))),
% 26.31/26.53      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 26.31/26.53  thf('11', plain,
% 26.31/26.53      (![X0 : $i]:
% 26.31/26.53         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 26.31/26.53           = (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 26.31/26.53      inference('sup-', [status(thm)], ['9', '10'])).
% 26.31/26.53  thf('12', plain,
% 26.31/26.53      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 26.31/26.53          (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 26.31/26.53      inference('demod', [status(thm)], ['4', '11'])).
% 26.31/26.53  thf('13', plain,
% 26.31/26.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 26.31/26.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.31/26.53  thf('14', plain,
% 26.31/26.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 26.31/26.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.31/26.53  thf(dt_k7_subset_1, axiom,
% 26.31/26.53    (![A:$i,B:$i,C:$i]:
% 26.31/26.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 26.31/26.53       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 26.31/26.53  thf('15', plain,
% 26.31/26.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 26.31/26.53         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 26.31/26.53          | (m1_subset_1 @ (k7_subset_1 @ X22 @ X21 @ X23) @ 
% 26.31/26.53             (k1_zfmisc_1 @ X22)))),
% 26.31/26.53      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 26.31/26.53  thf('16', plain,
% 26.31/26.53      (![X0 : $i]:
% 26.31/26.53         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 26.31/26.53          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 26.31/26.54      inference('sup-', [status(thm)], ['14', '15'])).
% 26.31/26.54  thf('17', plain,
% 26.31/26.54      (![X0 : $i]:
% 26.31/26.54         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 26.31/26.54           = (k4_xboole_0 @ sk_B @ X0))),
% 26.31/26.54      inference('sup-', [status(thm)], ['1', '2'])).
% 26.31/26.54  thf('18', plain,
% 26.31/26.54      (![X0 : $i]:
% 26.31/26.54         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 26.31/26.54          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 26.31/26.54      inference('demod', [status(thm)], ['16', '17'])).
% 26.31/26.54  thf(t48_tops_1, axiom,
% 26.31/26.54    (![A:$i]:
% 26.31/26.54     ( ( l1_pre_topc @ A ) =>
% 26.31/26.54       ( ![B:$i]:
% 26.31/26.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 26.31/26.54           ( ![C:$i]:
% 26.31/26.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 26.31/26.54               ( ( r1_tarski @ B @ C ) =>
% 26.31/26.54                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 26.31/26.54  thf('19', plain,
% 26.31/26.54      (![X31 : $i, X32 : $i, X33 : $i]:
% 26.31/26.54         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 26.31/26.54          | ~ (r1_tarski @ X31 @ X33)
% 26.31/26.54          | (r1_tarski @ (k1_tops_1 @ X32 @ X31) @ (k1_tops_1 @ X32 @ X33))
% 26.31/26.54          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 26.31/26.54          | ~ (l1_pre_topc @ X32))),
% 26.31/26.54      inference('cnf', [status(esa)], [t48_tops_1])).
% 26.31/26.54  thf('20', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i]:
% 26.31/26.54         (~ (l1_pre_topc @ sk_A)
% 26.31/26.54          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 26.31/26.54          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 26.31/26.54             (k1_tops_1 @ sk_A @ X1))
% 26.31/26.54          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 26.31/26.54      inference('sup-', [status(thm)], ['18', '19'])).
% 26.31/26.54  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 26.31/26.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.31/26.54  thf('22', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i]:
% 26.31/26.54         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 26.31/26.54          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 26.31/26.54             (k1_tops_1 @ sk_A @ X1))
% 26.31/26.54          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 26.31/26.54      inference('demod', [status(thm)], ['20', '21'])).
% 26.31/26.54  thf('23', plain,
% 26.31/26.54      (![X0 : $i]:
% 26.31/26.54         (~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_B)
% 26.31/26.54          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 26.31/26.54             (k1_tops_1 @ sk_A @ sk_B)))),
% 26.31/26.54      inference('sup-', [status(thm)], ['13', '22'])).
% 26.31/26.54  thf(t36_xboole_1, axiom,
% 26.31/26.54    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 26.31/26.54  thf('24', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 26.31/26.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 26.31/26.54  thf('25', plain,
% 26.31/26.54      (![X0 : $i]:
% 26.31/26.54         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 26.31/26.54          (k1_tops_1 @ sk_A @ sk_B))),
% 26.31/26.54      inference('demod', [status(thm)], ['23', '24'])).
% 26.31/26.54  thf('26', plain,
% 26.31/26.54      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 26.31/26.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.31/26.54  thf(t44_tops_1, axiom,
% 26.31/26.54    (![A:$i]:
% 26.31/26.54     ( ( l1_pre_topc @ A ) =>
% 26.31/26.54       ( ![B:$i]:
% 26.31/26.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 26.31/26.54           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 26.31/26.54  thf('27', plain,
% 26.31/26.54      (![X29 : $i, X30 : $i]:
% 26.31/26.54         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 26.31/26.54          | (r1_tarski @ (k1_tops_1 @ X30 @ X29) @ X29)
% 26.31/26.54          | ~ (l1_pre_topc @ X30))),
% 26.31/26.54      inference('cnf', [status(esa)], [t44_tops_1])).
% 26.31/26.54  thf('28', plain,
% 26.31/26.54      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 26.31/26.54      inference('sup-', [status(thm)], ['26', '27'])).
% 26.31/26.54  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 26.31/26.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.31/26.54  thf('30', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 26.31/26.54      inference('demod', [status(thm)], ['28', '29'])).
% 26.31/26.54  thf('31', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 26.31/26.54      inference('demod', [status(thm)], ['28', '29'])).
% 26.31/26.54  thf(t85_xboole_1, axiom,
% 26.31/26.54    (![A:$i,B:$i,C:$i]:
% 26.31/26.54     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 26.31/26.54  thf('32', plain,
% 26.31/26.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 26.31/26.54         (~ (r1_tarski @ X15 @ X16)
% 26.31/26.54          | (r1_xboole_0 @ X15 @ (k4_xboole_0 @ X17 @ X16)))),
% 26.31/26.54      inference('cnf', [status(esa)], [t85_xboole_1])).
% 26.31/26.54  thf('33', plain,
% 26.31/26.54      (![X0 : $i]:
% 26.31/26.54         (r1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C) @ (k4_xboole_0 @ X0 @ sk_C))),
% 26.31/26.54      inference('sup-', [status(thm)], ['31', '32'])).
% 26.31/26.54  thf(t86_xboole_1, axiom,
% 26.31/26.54    (![A:$i,B:$i,C:$i]:
% 26.31/26.54     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 26.31/26.54       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 26.31/26.54  thf('34', plain,
% 26.31/26.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 26.31/26.54         (~ (r1_tarski @ X18 @ X19)
% 26.31/26.54          | ~ (r1_xboole_0 @ X18 @ X20)
% 26.31/26.54          | (r1_tarski @ X18 @ (k4_xboole_0 @ X19 @ X20)))),
% 26.31/26.54      inference('cnf', [status(esa)], [t86_xboole_1])).
% 26.31/26.54  thf('35', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i]:
% 26.31/26.54         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 26.31/26.54           (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ sk_C)))
% 26.31/26.54          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ X1))),
% 26.31/26.54      inference('sup-', [status(thm)], ['33', '34'])).
% 26.31/26.54  thf('36', plain,
% 26.31/26.54      (![X0 : $i]:
% 26.31/26.54         (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 26.31/26.54          (k4_xboole_0 @ sk_C @ (k4_xboole_0 @ X0 @ sk_C)))),
% 26.31/26.54      inference('sup-', [status(thm)], ['30', '35'])).
% 26.31/26.54  thf('37', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 26.31/26.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 26.31/26.54  thf('38', plain,
% 26.31/26.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 26.31/26.54         (~ (r1_tarski @ X15 @ X16)
% 26.31/26.54          | (r1_xboole_0 @ X15 @ (k4_xboole_0 @ X17 @ X16)))),
% 26.31/26.54      inference('cnf', [status(esa)], [t85_xboole_1])).
% 26.31/26.54  thf('39', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.31/26.54         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X0))),
% 26.31/26.54      inference('sup-', [status(thm)], ['37', '38'])).
% 26.31/26.54  thf('40', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 26.31/26.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 26.31/26.54  thf('41', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.31/26.54         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X2 @ X0))),
% 26.31/26.54      inference('sup-', [status(thm)], ['37', '38'])).
% 26.31/26.54  thf('42', plain,
% 26.31/26.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 26.31/26.54         (~ (r1_tarski @ X18 @ X19)
% 26.31/26.54          | ~ (r1_xboole_0 @ X18 @ X20)
% 26.31/26.54          | (r1_tarski @ X18 @ (k4_xboole_0 @ X19 @ X20)))),
% 26.31/26.54      inference('cnf', [status(esa)], [t86_xboole_1])).
% 26.31/26.54  thf('43', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 26.31/26.54         ((r1_tarski @ (k4_xboole_0 @ X0 @ X2) @ 
% 26.31/26.54           (k4_xboole_0 @ X3 @ (k4_xboole_0 @ X1 @ X0)))
% 26.31/26.54          | ~ (r1_tarski @ (k4_xboole_0 @ X0 @ X2) @ X3))),
% 26.31/26.54      inference('sup-', [status(thm)], ['41', '42'])).
% 26.31/26.54  thf('44', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.31/26.54         (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ 
% 26.31/26.54          (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ X0)))),
% 26.31/26.54      inference('sup-', [status(thm)], ['40', '43'])).
% 26.31/26.54  thf(t64_xboole_1, axiom,
% 26.31/26.54    (![A:$i,B:$i,C:$i,D:$i]:
% 26.31/26.54     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 26.31/26.54         ( r1_xboole_0 @ B @ D ) ) =>
% 26.31/26.54       ( r1_xboole_0 @ A @ C ) ))).
% 26.31/26.54  thf('45', plain,
% 26.31/26.54      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 26.31/26.54         ((r1_xboole_0 @ X11 @ X12)
% 26.31/26.54          | ~ (r1_tarski @ X11 @ X13)
% 26.31/26.54          | ~ (r1_tarski @ X12 @ X14)
% 26.31/26.54          | ~ (r1_xboole_0 @ X13 @ X14))),
% 26.31/26.54      inference('cnf', [status(esa)], [t64_xboole_1])).
% 26.31/26.54  thf('46', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 26.31/26.54         (~ (r1_xboole_0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X3)
% 26.31/26.54          | ~ (r1_tarski @ X4 @ X3)
% 26.31/26.54          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X4))),
% 26.31/26.54      inference('sup-', [status(thm)], ['44', '45'])).
% 26.31/26.54  thf('47', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X3 : $i, X4 : $i]:
% 26.31/26.54         ((r1_xboole_0 @ (k4_xboole_0 @ X0 @ X4) @ X3)
% 26.31/26.54          | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ X1 @ X0)))),
% 26.31/26.54      inference('sup-', [status(thm)], ['39', '46'])).
% 26.31/26.54  thf('48', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i]:
% 26.31/26.54         (r1_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ X1) @ 
% 26.31/26.54          (k1_tops_1 @ sk_A @ sk_C))),
% 26.31/26.54      inference('sup-', [status(thm)], ['36', '47'])).
% 26.31/26.54  thf('49', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 26.31/26.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 26.31/26.54  thf('50', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 26.31/26.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 26.31/26.54  thf(t44_xboole_1, axiom,
% 26.31/26.54    (![A:$i,B:$i,C:$i]:
% 26.31/26.54     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 26.31/26.54       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 26.31/26.54  thf('51', plain,
% 26.31/26.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 26.31/26.54         ((r1_tarski @ X5 @ (k2_xboole_0 @ X6 @ X7))
% 26.31/26.54          | ~ (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X7))),
% 26.31/26.54      inference('cnf', [status(esa)], [t44_xboole_1])).
% 26.31/26.54  thf('52', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 26.31/26.54      inference('sup-', [status(thm)], ['50', '51'])).
% 26.31/26.54  thf('53', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 26.31/26.54      inference('sup-', [status(thm)], ['50', '51'])).
% 26.31/26.54  thf('54', plain,
% 26.31/26.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 26.31/26.54         (~ (r1_tarski @ X15 @ X16)
% 26.31/26.54          | (r1_xboole_0 @ X15 @ (k4_xboole_0 @ X17 @ X16)))),
% 26.31/26.54      inference('cnf', [status(esa)], [t85_xboole_1])).
% 26.31/26.54  thf('55', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.31/26.54         (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 26.31/26.54      inference('sup-', [status(thm)], ['53', '54'])).
% 26.31/26.54  thf('56', plain,
% 26.31/26.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 26.31/26.54         (~ (r1_tarski @ X18 @ X19)
% 26.31/26.54          | ~ (r1_xboole_0 @ X18 @ X20)
% 26.31/26.54          | (r1_tarski @ X18 @ (k4_xboole_0 @ X19 @ X20)))),
% 26.31/26.54      inference('cnf', [status(esa)], [t86_xboole_1])).
% 26.31/26.54  thf('57', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 26.31/26.54         ((r1_tarski @ X0 @ 
% 26.31/26.54           (k4_xboole_0 @ X3 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 26.31/26.54          | ~ (r1_tarski @ X0 @ X3))),
% 26.31/26.54      inference('sup-', [status(thm)], ['55', '56'])).
% 26.31/26.54  thf('58', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 26.31/26.54         (r1_tarski @ X0 @ 
% 26.31/26.54          (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ 
% 26.31/26.54           (k4_xboole_0 @ X3 @ (k2_xboole_0 @ X2 @ X0))))),
% 26.31/26.54      inference('sup-', [status(thm)], ['52', '57'])).
% 26.31/26.54  thf('59', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 26.31/26.54         ((r1_tarski @ X0 @ 
% 26.31/26.54           (k4_xboole_0 @ X3 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))))
% 26.31/26.54          | ~ (r1_tarski @ X0 @ X3))),
% 26.31/26.54      inference('sup-', [status(thm)], ['55', '56'])).
% 26.31/26.54  thf('60', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 26.31/26.54         (r1_tarski @ X0 @ 
% 26.31/26.54          (k4_xboole_0 @ 
% 26.31/26.54           (k4_xboole_0 @ (k2_xboole_0 @ X3 @ X0) @ 
% 26.31/26.54            (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))) @ 
% 26.31/26.54           (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X4 @ X0))))),
% 26.31/26.54      inference('sup-', [status(thm)], ['58', '59'])).
% 26.31/26.54  thf('61', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 26.31/26.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 26.31/26.54  thf(t43_xboole_1, axiom,
% 26.31/26.54    (![A:$i,B:$i,C:$i]:
% 26.31/26.54     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 26.31/26.54       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 26.31/26.54  thf('62', plain,
% 26.31/26.54      (![X2 : $i, X3 : $i, X4 : $i]:
% 26.31/26.54         ((r1_tarski @ (k4_xboole_0 @ X2 @ X3) @ X4)
% 26.31/26.54          | ~ (r1_tarski @ X2 @ (k2_xboole_0 @ X3 @ X4)))),
% 26.31/26.54      inference('cnf', [status(esa)], [t43_xboole_1])).
% 26.31/26.54  thf('63', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.31/26.54         (r1_tarski @ 
% 26.31/26.54          (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2) @ X1) @ 
% 26.31/26.54          X0)),
% 26.31/26.54      inference('sup-', [status(thm)], ['61', '62'])).
% 26.31/26.54  thf('64', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.31/26.54         (r1_tarski @ 
% 26.31/26.54          (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2) @ X1) @ 
% 26.31/26.54          X0)),
% 26.31/26.54      inference('sup-', [status(thm)], ['61', '62'])).
% 26.31/26.54  thf('65', plain,
% 26.31/26.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 26.31/26.54         (~ (r1_tarski @ X15 @ X16)
% 26.31/26.54          | (r1_xboole_0 @ X15 @ (k4_xboole_0 @ X17 @ X16)))),
% 26.31/26.54      inference('cnf', [status(esa)], [t85_xboole_1])).
% 26.31/26.54  thf('66', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 26.31/26.54         (r1_xboole_0 @ 
% 26.31/26.54          (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2) @ X1) @ 
% 26.31/26.54          (k4_xboole_0 @ X3 @ X0))),
% 26.31/26.54      inference('sup-', [status(thm)], ['64', '65'])).
% 26.31/26.54  thf('67', plain,
% 26.31/26.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 26.31/26.54         (~ (r1_tarski @ X18 @ X19)
% 26.31/26.54          | ~ (r1_xboole_0 @ X18 @ X20)
% 26.31/26.54          | (r1_tarski @ X18 @ (k4_xboole_0 @ X19 @ X20)))),
% 26.31/26.54      inference('cnf', [status(esa)], [t86_xboole_1])).
% 26.31/26.54  thf('68', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 26.31/26.54         ((r1_tarski @ 
% 26.31/26.54           (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ X3) @ X2) @ 
% 26.31/26.54           (k4_xboole_0 @ X4 @ (k4_xboole_0 @ X1 @ X0)))
% 26.31/26.54          | ~ (r1_tarski @ 
% 26.31/26.54               (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ X3) @ X2) @ 
% 26.31/26.54               X4))),
% 26.31/26.54      inference('sup-', [status(thm)], ['66', '67'])).
% 26.31/26.54  thf('69', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 26.31/26.54         (r1_tarski @ 
% 26.31/26.54          (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2) @ X1) @ 
% 26.31/26.54          (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X3 @ X0)))),
% 26.31/26.54      inference('sup-', [status(thm)], ['63', '68'])).
% 26.31/26.54  thf('70', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X3 : $i, X4 : $i]:
% 26.31/26.54         ((r1_xboole_0 @ (k4_xboole_0 @ X0 @ X4) @ X3)
% 26.31/26.54          | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ X1 @ X0)))),
% 26.31/26.54      inference('sup-', [status(thm)], ['39', '46'])).
% 26.31/26.54  thf('71', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 26.31/26.54         (r1_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X4) @ 
% 26.31/26.54          (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ X3) @ X2))),
% 26.31/26.54      inference('sup-', [status(thm)], ['69', '70'])).
% 26.31/26.54  thf('72', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 26.31/26.54         (~ (r1_xboole_0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X3)
% 26.31/26.54          | ~ (r1_tarski @ X4 @ X3)
% 26.31/26.54          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X4))),
% 26.31/26.54      inference('sup-', [status(thm)], ['44', '45'])).
% 26.31/26.54  thf('73', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X5 : $i, X6 : $i]:
% 26.31/26.54         ((r1_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X3 @ X2) @ X6) @ X5)
% 26.31/26.54          | ~ (r1_tarski @ X5 @ 
% 26.31/26.54               (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X2) @ X1) @ X0)))),
% 26.31/26.54      inference('sup-', [status(thm)], ['71', '72'])).
% 26.31/26.54  thf('74', plain,
% 26.31/26.54      (![X0 : $i, X5 : $i, X6 : $i]:
% 26.31/26.54         (r1_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X6 @ X0) @ X5) @ X0)),
% 26.31/26.54      inference('sup-', [status(thm)], ['60', '73'])).
% 26.31/26.54  thf('75', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 26.31/26.54         (r1_tarski @ 
% 26.31/26.54          (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2) @ X1) @ 
% 26.31/26.54          (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X3 @ X0)))),
% 26.31/26.54      inference('sup-', [status(thm)], ['63', '68'])).
% 26.31/26.54  thf(t63_xboole_1, axiom,
% 26.31/26.54    (![A:$i,B:$i,C:$i]:
% 26.31/26.54     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 26.31/26.54       ( r1_xboole_0 @ A @ C ) ))).
% 26.31/26.54  thf('76', plain,
% 26.31/26.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 26.31/26.54         (~ (r1_tarski @ X8 @ X9)
% 26.31/26.54          | ~ (r1_xboole_0 @ X9 @ X10)
% 26.31/26.54          | (r1_xboole_0 @ X8 @ X10))),
% 26.31/26.54      inference('cnf', [status(esa)], [t63_xboole_1])).
% 26.31/26.54  thf('77', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 26.31/26.54         ((r1_xboole_0 @ 
% 26.31/26.54           (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X2 @ X0) @ X3) @ X2) @ 
% 26.31/26.54           X4)
% 26.31/26.54          | ~ (r1_xboole_0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X4))),
% 26.31/26.54      inference('sup-', [status(thm)], ['75', '76'])).
% 26.31/26.54  thf('78', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X3 : $i, X4 : $i]:
% 26.31/26.54         (r1_xboole_0 @ 
% 26.31/26.54          (k4_xboole_0 @ 
% 26.31/26.54           (k4_xboole_0 @ (k2_xboole_0 @ X3 @ (k4_xboole_0 @ X1 @ X0)) @ X4) @ 
% 26.31/26.54           X3) @ 
% 26.31/26.54          X0)),
% 26.31/26.54      inference('sup-', [status(thm)], ['74', '77'])).
% 26.31/26.54  thf('79', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 26.31/26.54         (r1_tarski @ X0 @ 
% 26.31/26.54          (k4_xboole_0 @ 
% 26.31/26.54           (k4_xboole_0 @ (k2_xboole_0 @ X3 @ X0) @ 
% 26.31/26.54            (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))) @ 
% 26.31/26.54           (k4_xboole_0 @ X5 @ (k2_xboole_0 @ X4 @ X0))))),
% 26.31/26.54      inference('sup-', [status(thm)], ['58', '59'])).
% 26.31/26.54  thf('80', plain,
% 26.31/26.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 26.31/26.54         (~ (r1_tarski @ X8 @ X9)
% 26.31/26.54          | ~ (r1_xboole_0 @ X9 @ X10)
% 26.31/26.54          | (r1_xboole_0 @ X8 @ X10))),
% 26.31/26.54      inference('cnf', [status(esa)], [t63_xboole_1])).
% 26.31/26.54  thf('81', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 26.31/26.54         ((r1_xboole_0 @ X0 @ X6)
% 26.31/26.54          | ~ (r1_xboole_0 @ 
% 26.31/26.54               (k4_xboole_0 @ 
% 26.31/26.54                (k4_xboole_0 @ (k2_xboole_0 @ X5 @ X0) @ 
% 26.31/26.54                 (k4_xboole_0 @ X4 @ (k2_xboole_0 @ X3 @ X0))) @ 
% 26.31/26.54                (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))) @ 
% 26.31/26.54               X6))),
% 26.31/26.54      inference('sup-', [status(thm)], ['79', '80'])).
% 26.31/26.54  thf('82', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 26.31/26.54      inference('sup-', [status(thm)], ['78', '81'])).
% 26.31/26.54  thf('83', plain,
% 26.31/26.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 26.31/26.54         (~ (r1_tarski @ X18 @ X19)
% 26.31/26.54          | ~ (r1_xboole_0 @ X18 @ X20)
% 26.31/26.54          | (r1_tarski @ X18 @ (k4_xboole_0 @ X19 @ X20)))),
% 26.31/26.54      inference('cnf', [status(esa)], [t86_xboole_1])).
% 26.31/26.54  thf('84', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.31/26.54         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X0))
% 26.31/26.54          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 26.31/26.54      inference('sup-', [status(thm)], ['82', '83'])).
% 26.31/26.54  thf('85', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i]:
% 26.31/26.54         (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X1))),
% 26.31/26.54      inference('sup-', [status(thm)], ['49', '84'])).
% 26.31/26.54  thf('86', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.31/26.54         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X0))
% 26.31/26.54          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 26.31/26.54      inference('sup-', [status(thm)], ['82', '83'])).
% 26.31/26.54  thf('87', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i]:
% 26.31/26.54         (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ 
% 26.31/26.54          (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 26.31/26.54      inference('sup-', [status(thm)], ['85', '86'])).
% 26.31/26.54  thf('88', plain,
% 26.31/26.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 26.31/26.54         (~ (r1_tarski @ X8 @ X9)
% 26.31/26.54          | ~ (r1_xboole_0 @ X9 @ X10)
% 26.31/26.54          | (r1_xboole_0 @ X8 @ X10))),
% 26.31/26.54      inference('cnf', [status(esa)], [t63_xboole_1])).
% 26.31/26.54  thf('89', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.31/26.54         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 26.31/26.54          | ~ (r1_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) @ X2))),
% 26.31/26.54      inference('sup-', [status(thm)], ['87', '88'])).
% 26.31/26.54  thf('90', plain,
% 26.31/26.54      (![X0 : $i]:
% 26.31/26.54         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ (k1_tops_1 @ sk_A @ sk_C))),
% 26.31/26.54      inference('sup-', [status(thm)], ['48', '89'])).
% 26.31/26.54  thf('91', plain,
% 26.31/26.54      (![X0 : $i]:
% 26.31/26.54         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 26.31/26.54          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 26.31/26.54      inference('demod', [status(thm)], ['16', '17'])).
% 26.31/26.54  thf('92', plain,
% 26.31/26.54      (![X29 : $i, X30 : $i]:
% 26.31/26.54         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 26.31/26.54          | (r1_tarski @ (k1_tops_1 @ X30 @ X29) @ X29)
% 26.31/26.54          | ~ (l1_pre_topc @ X30))),
% 26.31/26.54      inference('cnf', [status(esa)], [t44_tops_1])).
% 26.31/26.54  thf('93', plain,
% 26.31/26.54      (![X0 : $i]:
% 26.31/26.54         (~ (l1_pre_topc @ sk_A)
% 26.31/26.54          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 26.31/26.54             (k4_xboole_0 @ sk_B @ X0)))),
% 26.31/26.54      inference('sup-', [status(thm)], ['91', '92'])).
% 26.31/26.54  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 26.31/26.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.31/26.54  thf('95', plain,
% 26.31/26.54      (![X0 : $i]:
% 26.31/26.54         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 26.31/26.54          (k4_xboole_0 @ sk_B @ X0))),
% 26.31/26.54      inference('demod', [status(thm)], ['93', '94'])).
% 26.31/26.54  thf('96', plain,
% 26.31/26.54      (![X8 : $i, X9 : $i, X10 : $i]:
% 26.31/26.54         (~ (r1_tarski @ X8 @ X9)
% 26.31/26.54          | ~ (r1_xboole_0 @ X9 @ X10)
% 26.31/26.54          | (r1_xboole_0 @ X8 @ X10))),
% 26.31/26.54      inference('cnf', [status(esa)], [t63_xboole_1])).
% 26.31/26.54  thf('97', plain,
% 26.31/26.54      (![X0 : $i, X1 : $i]:
% 26.31/26.54         ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ X1)
% 26.31/26.54          | ~ (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 26.31/26.54      inference('sup-', [status(thm)], ['95', '96'])).
% 26.31/26.54  thf('98', plain,
% 26.31/26.54      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 26.31/26.54        (k1_tops_1 @ sk_A @ sk_C))),
% 26.31/26.54      inference('sup-', [status(thm)], ['90', '97'])).
% 26.31/26.54  thf('99', plain,
% 26.31/26.54      (![X18 : $i, X19 : $i, X20 : $i]:
% 26.31/26.54         (~ (r1_tarski @ X18 @ X19)
% 26.31/26.54          | ~ (r1_xboole_0 @ X18 @ X20)
% 26.31/26.54          | (r1_tarski @ X18 @ (k4_xboole_0 @ X19 @ X20)))),
% 26.31/26.54      inference('cnf', [status(esa)], [t86_xboole_1])).
% 26.31/26.54  thf('100', plain,
% 26.31/26.54      (![X0 : $i]:
% 26.31/26.54         ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 26.31/26.54           (k4_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))
% 26.31/26.54          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 26.31/26.54               X0))),
% 26.31/26.54      inference('sup-', [status(thm)], ['98', '99'])).
% 26.31/26.54  thf('101', plain,
% 26.31/26.54      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 26.31/26.54        (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 26.31/26.54      inference('sup-', [status(thm)], ['25', '100'])).
% 26.31/26.54  thf('102', plain, ($false), inference('demod', [status(thm)], ['12', '101'])).
% 26.31/26.54  
% 26.31/26.54  % SZS output end Refutation
% 26.31/26.54  
% 26.31/26.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
