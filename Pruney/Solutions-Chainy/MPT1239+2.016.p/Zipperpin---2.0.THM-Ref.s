%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aXxmoQCrFD

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:03 EST 2020

% Result     : Theorem 23.64s
% Output     : Refutation 23.64s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 275 expanded)
%              Number of leaves         :   26 (  94 expanded)
%              Depth                    :   15
%              Number of atoms          : 1176 (2858 expanded)
%              Number of equality atoms :   28 (  58 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X27 @ X26 ) @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
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

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('14',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('33',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( r1_tarski @ X28 @ X30 )
      | ( r1_tarski @ ( k1_tops_1 @ X29 @ X28 ) @ ( k1_tops_1 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['23','36'])).

thf('38',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('41',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X27 @ X26 ) @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('45',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X3 @ X5 )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('47',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X17 @ X19 )
      | ( r1_tarski @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X27 @ X26 ) @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('52',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('56',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['54','55'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('58',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('60',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X3 @ X5 )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X17 @ X19 )
      | ( r1_tarski @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('71',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('72',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['57'])).

thf(t64_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D )
        & ( r1_xboole_0 @ B @ D ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('75',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_tarski @ X13 @ X15 )
      | ~ ( r1_tarski @ X14 @ X16 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t64_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ X1 )
      | ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup-',[status(thm)],['70','77'])).

thf('79',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X17 @ X19 )
      | ( r1_tarski @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ ( k4_xboole_0 @ X3 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['69','80'])).

thf('82',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['68','83'])).

thf('85',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['56','87'])).

thf('89',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['54','55'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
      = ( k4_xboole_0 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('92',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('97',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X3 @ X5 )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X17 @ X19 )
      | ( r1_tarski @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) @ ( k4_xboole_0 @ X3 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['95','100'])).

thf('102',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) )
      | ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['95','100'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      | ( r1_tarski @ X3 @ ( k4_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k4_xboole_0 @ X0 @ sk_C ) )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['90','107'])).

thf('109',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['49','108'])).

thf('110',plain,(
    $false ),
    inference(demod,[status(thm)],['22','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aXxmoQCrFD
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:52:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 23.64/23.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 23.64/23.81  % Solved by: fo/fo7.sh
% 23.64/23.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 23.64/23.81  % done 20412 iterations in 23.353s
% 23.64/23.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 23.64/23.81  % SZS output start Refutation
% 23.64/23.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 23.64/23.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 23.64/23.81  thf(sk_C_type, type, sk_C: $i).
% 23.64/23.81  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 23.64/23.81  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 23.64/23.81  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 23.64/23.81  thf(sk_B_type, type, sk_B: $i).
% 23.64/23.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 23.64/23.81  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 23.64/23.81  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 23.64/23.81  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 23.64/23.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 23.64/23.81  thf(sk_A_type, type, sk_A: $i).
% 23.64/23.81  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 23.64/23.81  thf(t50_tops_1, conjecture,
% 23.64/23.81    (![A:$i]:
% 23.64/23.81     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 23.64/23.81       ( ![B:$i]:
% 23.64/23.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 23.64/23.81           ( ![C:$i]:
% 23.64/23.81             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 23.64/23.81               ( r1_tarski @
% 23.64/23.81                 ( k1_tops_1 @
% 23.64/23.81                   A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 23.64/23.81                 ( k7_subset_1 @
% 23.64/23.81                   ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 23.64/23.81                   ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 23.64/23.81  thf(zf_stmt_0, negated_conjecture,
% 23.64/23.81    (~( ![A:$i]:
% 23.64/23.81        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 23.64/23.81          ( ![B:$i]:
% 23.64/23.81            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 23.64/23.81              ( ![C:$i]:
% 23.64/23.81                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 23.64/23.81                  ( r1_tarski @
% 23.64/23.81                    ( k1_tops_1 @
% 23.64/23.81                      A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 23.64/23.81                    ( k7_subset_1 @
% 23.64/23.81                      ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 23.64/23.81                      ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 23.64/23.81    inference('cnf.neg', [status(esa)], [t50_tops_1])).
% 23.64/23.81  thf('0', plain,
% 23.64/23.81      (~ (r1_tarski @ 
% 23.64/23.81          (k1_tops_1 @ sk_A @ 
% 23.64/23.81           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 23.64/23.81          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 23.64/23.81           (k1_tops_1 @ sk_A @ sk_C)))),
% 23.64/23.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.64/23.81  thf('1', plain,
% 23.64/23.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 23.64/23.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.64/23.81  thf(redefinition_k7_subset_1, axiom,
% 23.64/23.81    (![A:$i,B:$i,C:$i]:
% 23.64/23.81     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 23.64/23.81       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 23.64/23.81  thf('2', plain,
% 23.64/23.81      (![X20 : $i, X21 : $i, X22 : $i]:
% 23.64/23.81         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 23.64/23.81          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 23.64/23.81      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 23.64/23.81  thf('3', plain,
% 23.64/23.81      (![X0 : $i]:
% 23.64/23.81         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 23.64/23.81           = (k4_xboole_0 @ sk_B @ X0))),
% 23.64/23.81      inference('sup-', [status(thm)], ['1', '2'])).
% 23.64/23.81  thf('4', plain,
% 23.64/23.81      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 23.64/23.81          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 23.64/23.81           (k1_tops_1 @ sk_A @ sk_C)))),
% 23.64/23.81      inference('demod', [status(thm)], ['0', '3'])).
% 23.64/23.81  thf('5', plain,
% 23.64/23.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 23.64/23.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.64/23.81  thf(t3_subset, axiom,
% 23.64/23.81    (![A:$i,B:$i]:
% 23.64/23.81     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 23.64/23.81  thf('6', plain,
% 23.64/23.81      (![X23 : $i, X24 : $i]:
% 23.64/23.81         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 23.64/23.81      inference('cnf', [status(esa)], [t3_subset])).
% 23.64/23.81  thf('7', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 23.64/23.81      inference('sup-', [status(thm)], ['5', '6'])).
% 23.64/23.81  thf('8', plain,
% 23.64/23.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 23.64/23.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.64/23.81  thf(t44_tops_1, axiom,
% 23.64/23.81    (![A:$i]:
% 23.64/23.81     ( ( l1_pre_topc @ A ) =>
% 23.64/23.81       ( ![B:$i]:
% 23.64/23.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 23.64/23.81           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 23.64/23.81  thf('9', plain,
% 23.64/23.81      (![X26 : $i, X27 : $i]:
% 23.64/23.81         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 23.64/23.81          | (r1_tarski @ (k1_tops_1 @ X27 @ X26) @ X26)
% 23.64/23.81          | ~ (l1_pre_topc @ X27))),
% 23.64/23.81      inference('cnf', [status(esa)], [t44_tops_1])).
% 23.64/23.81  thf('10', plain,
% 23.64/23.81      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 23.64/23.81      inference('sup-', [status(thm)], ['8', '9'])).
% 23.64/23.81  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 23.64/23.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.64/23.81  thf('12', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 23.64/23.81      inference('demod', [status(thm)], ['10', '11'])).
% 23.64/23.81  thf(t12_xboole_1, axiom,
% 23.64/23.81    (![A:$i,B:$i]:
% 23.64/23.81     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 23.64/23.81  thf('13', plain,
% 23.64/23.81      (![X9 : $i, X10 : $i]:
% 23.64/23.81         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 23.64/23.81      inference('cnf', [status(esa)], [t12_xboole_1])).
% 23.64/23.81  thf('14', plain,
% 23.64/23.81      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B) = (sk_B))),
% 23.64/23.81      inference('sup-', [status(thm)], ['12', '13'])).
% 23.64/23.81  thf(t11_xboole_1, axiom,
% 23.64/23.81    (![A:$i,B:$i,C:$i]:
% 23.64/23.81     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 23.64/23.81  thf('15', plain,
% 23.64/23.81      (![X6 : $i, X7 : $i, X8 : $i]:
% 23.64/23.81         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 23.64/23.81      inference('cnf', [status(esa)], [t11_xboole_1])).
% 23.64/23.81  thf('16', plain,
% 23.64/23.81      (![X0 : $i]:
% 23.64/23.81         (~ (r1_tarski @ sk_B @ X0)
% 23.64/23.81          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 23.64/23.81      inference('sup-', [status(thm)], ['14', '15'])).
% 23.64/23.81  thf('17', plain,
% 23.64/23.81      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 23.64/23.81      inference('sup-', [status(thm)], ['7', '16'])).
% 23.64/23.81  thf('18', plain,
% 23.64/23.81      (![X23 : $i, X25 : $i]:
% 23.64/23.81         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 23.64/23.81      inference('cnf', [status(esa)], [t3_subset])).
% 23.64/23.81  thf('19', plain,
% 23.64/23.81      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 23.64/23.81        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 23.64/23.81      inference('sup-', [status(thm)], ['17', '18'])).
% 23.64/23.81  thf('20', plain,
% 23.64/23.81      (![X20 : $i, X21 : $i, X22 : $i]:
% 23.64/23.81         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 23.64/23.81          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 23.64/23.81      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 23.64/23.81  thf('21', plain,
% 23.64/23.81      (![X0 : $i]:
% 23.64/23.81         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 23.64/23.81           = (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 23.64/23.81      inference('sup-', [status(thm)], ['19', '20'])).
% 23.64/23.81  thf('22', plain,
% 23.64/23.81      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 23.64/23.81          (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 23.64/23.81      inference('demod', [status(thm)], ['4', '21'])).
% 23.64/23.81  thf('23', plain,
% 23.64/23.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 23.64/23.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.64/23.81  thf('24', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 23.64/23.81      inference('sup-', [status(thm)], ['5', '6'])).
% 23.64/23.81  thf(t36_xboole_1, axiom,
% 23.64/23.81    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 23.64/23.81  thf('25', plain,
% 23.64/23.81      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 23.64/23.81      inference('cnf', [status(esa)], [t36_xboole_1])).
% 23.64/23.81  thf('26', plain,
% 23.64/23.81      (![X9 : $i, X10 : $i]:
% 23.64/23.81         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 23.64/23.81      inference('cnf', [status(esa)], [t12_xboole_1])).
% 23.64/23.81  thf('27', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i]:
% 23.64/23.81         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 23.64/23.81      inference('sup-', [status(thm)], ['25', '26'])).
% 23.64/23.81  thf('28', plain,
% 23.64/23.81      (![X6 : $i, X7 : $i, X8 : $i]:
% 23.64/23.81         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 23.64/23.81      inference('cnf', [status(esa)], [t11_xboole_1])).
% 23.64/23.81  thf('29', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.64/23.81         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k4_xboole_0 @ X0 @ X2) @ X1))),
% 23.64/23.81      inference('sup-', [status(thm)], ['27', '28'])).
% 23.64/23.81  thf('30', plain,
% 23.64/23.81      (![X0 : $i]:
% 23.64/23.81         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 23.64/23.81      inference('sup-', [status(thm)], ['24', '29'])).
% 23.64/23.81  thf('31', plain,
% 23.64/23.81      (![X23 : $i, X25 : $i]:
% 23.64/23.81         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 23.64/23.81      inference('cnf', [status(esa)], [t3_subset])).
% 23.64/23.81  thf('32', plain,
% 23.64/23.81      (![X0 : $i]:
% 23.64/23.81         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 23.64/23.81          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 23.64/23.81      inference('sup-', [status(thm)], ['30', '31'])).
% 23.64/23.81  thf(t48_tops_1, axiom,
% 23.64/23.81    (![A:$i]:
% 23.64/23.81     ( ( l1_pre_topc @ A ) =>
% 23.64/23.81       ( ![B:$i]:
% 23.64/23.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 23.64/23.81           ( ![C:$i]:
% 23.64/23.81             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 23.64/23.81               ( ( r1_tarski @ B @ C ) =>
% 23.64/23.81                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 23.64/23.81  thf('33', plain,
% 23.64/23.81      (![X28 : $i, X29 : $i, X30 : $i]:
% 23.64/23.81         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 23.64/23.81          | ~ (r1_tarski @ X28 @ X30)
% 23.64/23.81          | (r1_tarski @ (k1_tops_1 @ X29 @ X28) @ (k1_tops_1 @ X29 @ X30))
% 23.64/23.81          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 23.64/23.81          | ~ (l1_pre_topc @ X29))),
% 23.64/23.81      inference('cnf', [status(esa)], [t48_tops_1])).
% 23.64/23.81  thf('34', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i]:
% 23.64/23.81         (~ (l1_pre_topc @ sk_A)
% 23.64/23.81          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 23.64/23.81          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 23.64/23.81             (k1_tops_1 @ sk_A @ X1))
% 23.64/23.81          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 23.64/23.81      inference('sup-', [status(thm)], ['32', '33'])).
% 23.64/23.81  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 23.64/23.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.64/23.81  thf('36', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i]:
% 23.64/23.81         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 23.64/23.81          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 23.64/23.81             (k1_tops_1 @ sk_A @ X1))
% 23.64/23.81          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 23.64/23.81      inference('demod', [status(thm)], ['34', '35'])).
% 23.64/23.81  thf('37', plain,
% 23.64/23.81      (![X0 : $i]:
% 23.64/23.81         (~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_B)
% 23.64/23.81          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 23.64/23.81             (k1_tops_1 @ sk_A @ sk_B)))),
% 23.64/23.81      inference('sup-', [status(thm)], ['23', '36'])).
% 23.64/23.81  thf('38', plain,
% 23.64/23.81      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 23.64/23.81      inference('cnf', [status(esa)], [t36_xboole_1])).
% 23.64/23.81  thf('39', plain,
% 23.64/23.81      (![X0 : $i]:
% 23.64/23.81         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 23.64/23.81          (k1_tops_1 @ sk_A @ sk_B))),
% 23.64/23.81      inference('demod', [status(thm)], ['37', '38'])).
% 23.64/23.81  thf('40', plain,
% 23.64/23.81      (![X0 : $i]:
% 23.64/23.81         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 23.64/23.81          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 23.64/23.81      inference('sup-', [status(thm)], ['30', '31'])).
% 23.64/23.81  thf('41', plain,
% 23.64/23.81      (![X26 : $i, X27 : $i]:
% 23.64/23.81         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 23.64/23.81          | (r1_tarski @ (k1_tops_1 @ X27 @ X26) @ X26)
% 23.64/23.81          | ~ (l1_pre_topc @ X27))),
% 23.64/23.81      inference('cnf', [status(esa)], [t44_tops_1])).
% 23.64/23.81  thf('42', plain,
% 23.64/23.81      (![X0 : $i]:
% 23.64/23.81         (~ (l1_pre_topc @ sk_A)
% 23.64/23.81          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 23.64/23.81             (k4_xboole_0 @ sk_B @ X0)))),
% 23.64/23.81      inference('sup-', [status(thm)], ['40', '41'])).
% 23.64/23.81  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 23.64/23.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.64/23.81  thf('44', plain,
% 23.64/23.81      (![X0 : $i]:
% 23.64/23.81         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 23.64/23.81          (k4_xboole_0 @ sk_B @ X0))),
% 23.64/23.81      inference('demod', [status(thm)], ['42', '43'])).
% 23.64/23.81  thf(t106_xboole_1, axiom,
% 23.64/23.81    (![A:$i,B:$i,C:$i]:
% 23.64/23.81     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 23.64/23.81       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 23.64/23.81  thf('45', plain,
% 23.64/23.81      (![X3 : $i, X4 : $i, X5 : $i]:
% 23.64/23.81         ((r1_xboole_0 @ X3 @ X5)
% 23.64/23.81          | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ X4 @ X5)))),
% 23.64/23.81      inference('cnf', [status(esa)], [t106_xboole_1])).
% 23.64/23.81  thf('46', plain,
% 23.64/23.81      (![X0 : $i]:
% 23.64/23.81         (r1_xboole_0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ X0)),
% 23.64/23.81      inference('sup-', [status(thm)], ['44', '45'])).
% 23.64/23.81  thf(t86_xboole_1, axiom,
% 23.64/23.81    (![A:$i,B:$i,C:$i]:
% 23.64/23.81     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 23.64/23.81       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 23.64/23.81  thf('47', plain,
% 23.64/23.81      (![X17 : $i, X18 : $i, X19 : $i]:
% 23.64/23.81         (~ (r1_tarski @ X17 @ X18)
% 23.64/23.81          | ~ (r1_xboole_0 @ X17 @ X19)
% 23.64/23.81          | (r1_tarski @ X17 @ (k4_xboole_0 @ X18 @ X19)))),
% 23.64/23.81      inference('cnf', [status(esa)], [t86_xboole_1])).
% 23.64/23.81  thf('48', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i]:
% 23.64/23.81         ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 23.64/23.81           (k4_xboole_0 @ X1 @ X0))
% 23.64/23.81          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ X1))),
% 23.64/23.81      inference('sup-', [status(thm)], ['46', '47'])).
% 23.64/23.81  thf('49', plain,
% 23.64/23.81      (![X0 : $i]:
% 23.64/23.81         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 23.64/23.81          (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 23.64/23.81      inference('sup-', [status(thm)], ['39', '48'])).
% 23.64/23.81  thf('50', plain,
% 23.64/23.81      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 23.64/23.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.64/23.81  thf('51', plain,
% 23.64/23.81      (![X26 : $i, X27 : $i]:
% 23.64/23.81         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 23.64/23.81          | (r1_tarski @ (k1_tops_1 @ X27 @ X26) @ X26)
% 23.64/23.81          | ~ (l1_pre_topc @ X27))),
% 23.64/23.81      inference('cnf', [status(esa)], [t44_tops_1])).
% 23.64/23.81  thf('52', plain,
% 23.64/23.81      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 23.64/23.81      inference('sup-', [status(thm)], ['50', '51'])).
% 23.64/23.81  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 23.64/23.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 23.64/23.81  thf('54', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 23.64/23.81      inference('demod', [status(thm)], ['52', '53'])).
% 23.64/23.81  thf('55', plain,
% 23.64/23.81      (![X9 : $i, X10 : $i]:
% 23.64/23.81         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 23.64/23.81      inference('cnf', [status(esa)], [t12_xboole_1])).
% 23.64/23.81  thf('56', plain,
% 23.64/23.81      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C) = (sk_C))),
% 23.64/23.81      inference('sup-', [status(thm)], ['54', '55'])).
% 23.64/23.81  thf(d10_xboole_0, axiom,
% 23.64/23.81    (![A:$i,B:$i]:
% 23.64/23.81     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 23.64/23.81  thf('57', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 23.64/23.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 23.64/23.81  thf('58', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 23.64/23.81      inference('simplify', [status(thm)], ['57'])).
% 23.64/23.81  thf('59', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 23.64/23.81      inference('simplify', [status(thm)], ['57'])).
% 23.64/23.81  thf('60', plain,
% 23.64/23.81      (![X3 : $i, X4 : $i, X5 : $i]:
% 23.64/23.81         ((r1_xboole_0 @ X3 @ X5)
% 23.64/23.81          | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ X4 @ X5)))),
% 23.64/23.81      inference('cnf', [status(esa)], [t106_xboole_1])).
% 23.64/23.81  thf('61', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 23.64/23.81      inference('sup-', [status(thm)], ['59', '60'])).
% 23.64/23.81  thf('62', plain,
% 23.64/23.81      (![X17 : $i, X18 : $i, X19 : $i]:
% 23.64/23.81         (~ (r1_tarski @ X17 @ X18)
% 23.64/23.81          | ~ (r1_xboole_0 @ X17 @ X19)
% 23.64/23.81          | (r1_tarski @ X17 @ (k4_xboole_0 @ X18 @ X19)))),
% 23.64/23.81      inference('cnf', [status(esa)], [t86_xboole_1])).
% 23.64/23.81  thf('63', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.64/23.81         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X0))
% 23.64/23.81          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 23.64/23.81      inference('sup-', [status(thm)], ['61', '62'])).
% 23.64/23.81  thf('64', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i]:
% 23.64/23.81         (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ 
% 23.64/23.81          (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 23.64/23.81      inference('sup-', [status(thm)], ['58', '63'])).
% 23.64/23.81  thf('65', plain,
% 23.64/23.81      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 23.64/23.81      inference('cnf', [status(esa)], [t36_xboole_1])).
% 23.64/23.81  thf('66', plain,
% 23.64/23.81      (![X0 : $i, X2 : $i]:
% 23.64/23.81         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 23.64/23.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 23.64/23.81  thf('67', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i]:
% 23.64/23.81         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 23.64/23.81          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 23.64/23.81      inference('sup-', [status(thm)], ['65', '66'])).
% 23.64/23.81  thf('68', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i]:
% 23.64/23.81         ((k4_xboole_0 @ X1 @ X0)
% 23.64/23.81           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 23.64/23.81      inference('sup-', [status(thm)], ['64', '67'])).
% 23.64/23.81  thf('69', plain,
% 23.64/23.81      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 23.64/23.81      inference('cnf', [status(esa)], [t36_xboole_1])).
% 23.64/23.81  thf('70', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 23.64/23.81      inference('sup-', [status(thm)], ['59', '60'])).
% 23.64/23.81  thf('71', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 23.64/23.81      inference('simplify', [status(thm)], ['57'])).
% 23.64/23.81  thf('72', plain,
% 23.64/23.81      (![X6 : $i, X7 : $i, X8 : $i]:
% 23.64/23.81         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 23.64/23.81      inference('cnf', [status(esa)], [t11_xboole_1])).
% 23.64/23.81  thf('73', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 23.64/23.81      inference('sup-', [status(thm)], ['71', '72'])).
% 23.64/23.81  thf('74', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 23.64/23.81      inference('simplify', [status(thm)], ['57'])).
% 23.64/23.81  thf(t64_xboole_1, axiom,
% 23.64/23.81    (![A:$i,B:$i,C:$i,D:$i]:
% 23.64/23.81     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 23.64/23.81         ( r1_xboole_0 @ B @ D ) ) =>
% 23.64/23.81       ( r1_xboole_0 @ A @ C ) ))).
% 23.64/23.81  thf('75', plain,
% 23.64/23.81      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 23.64/23.81         ((r1_xboole_0 @ X13 @ X14)
% 23.64/23.81          | ~ (r1_tarski @ X13 @ X15)
% 23.64/23.81          | ~ (r1_tarski @ X14 @ X16)
% 23.64/23.81          | ~ (r1_xboole_0 @ X15 @ X16))),
% 23.64/23.81      inference('cnf', [status(esa)], [t64_xboole_1])).
% 23.64/23.81  thf('76', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.64/23.81         (~ (r1_xboole_0 @ X0 @ X1)
% 23.64/23.81          | ~ (r1_tarski @ X2 @ X1)
% 23.64/23.81          | (r1_xboole_0 @ X0 @ X2))),
% 23.64/23.81      inference('sup-', [status(thm)], ['74', '75'])).
% 23.64/23.81  thf('77', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.64/23.81         ((r1_xboole_0 @ X2 @ X1)
% 23.64/23.81          | ~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 23.64/23.81      inference('sup-', [status(thm)], ['73', '76'])).
% 23.64/23.81  thf('78', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.64/23.81         (r1_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)),
% 23.64/23.81      inference('sup-', [status(thm)], ['70', '77'])).
% 23.64/23.81  thf('79', plain,
% 23.64/23.81      (![X17 : $i, X18 : $i, X19 : $i]:
% 23.64/23.81         (~ (r1_tarski @ X17 @ X18)
% 23.64/23.81          | ~ (r1_xboole_0 @ X17 @ X19)
% 23.64/23.81          | (r1_tarski @ X17 @ (k4_xboole_0 @ X18 @ X19)))),
% 23.64/23.81      inference('cnf', [status(esa)], [t86_xboole_1])).
% 23.64/23.81  thf('80', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 23.64/23.81         ((r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)) @ 
% 23.64/23.81           (k4_xboole_0 @ X3 @ X0))
% 23.64/23.81          | ~ (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)) @ X3))),
% 23.64/23.81      inference('sup-', [status(thm)], ['78', '79'])).
% 23.64/23.81  thf('81', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.64/23.81         (r1_tarski @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1)) @ 
% 23.64/23.81          (k4_xboole_0 @ X0 @ X2))),
% 23.64/23.81      inference('sup-', [status(thm)], ['69', '80'])).
% 23.64/23.81  thf('82', plain,
% 23.64/23.81      (![X0 : $i, X2 : $i]:
% 23.64/23.81         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 23.64/23.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 23.64/23.81  thf('83', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.64/23.81         (~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ 
% 23.64/23.81             (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)))
% 23.64/23.81          | ((k4_xboole_0 @ X1 @ X0)
% 23.64/23.81              = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))))),
% 23.64/23.81      inference('sup-', [status(thm)], ['81', '82'])).
% 23.64/23.81  thf('84', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.64/23.81         (~ (r1_tarski @ 
% 23.64/23.81             (k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1) @ 
% 23.64/23.81             (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 23.64/23.81          | ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)
% 23.64/23.81              = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 23.64/23.81                 (k2_xboole_0 @ X1 @ X0))))),
% 23.64/23.81      inference('sup-', [status(thm)], ['68', '83'])).
% 23.64/23.81  thf('85', plain,
% 23.64/23.81      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 23.64/23.81      inference('cnf', [status(esa)], [t36_xboole_1])).
% 23.64/23.81  thf('86', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i]:
% 23.64/23.81         ((k4_xboole_0 @ X1 @ X0)
% 23.64/23.81           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 23.64/23.81      inference('sup-', [status(thm)], ['64', '67'])).
% 23.64/23.81  thf('87', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.64/23.81         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)
% 23.64/23.81           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 23.64/23.81      inference('demod', [status(thm)], ['84', '85', '86'])).
% 23.64/23.81  thf('88', plain,
% 23.64/23.81      (![X0 : $i]:
% 23.64/23.81         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ (k1_tops_1 @ sk_A @ sk_C))
% 23.64/23.81           = (k4_xboole_0 @ X0 @ 
% 23.64/23.81              (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)))),
% 23.64/23.81      inference('sup+', [status(thm)], ['56', '87'])).
% 23.64/23.81  thf('89', plain,
% 23.64/23.81      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C) = (sk_C))),
% 23.64/23.81      inference('sup-', [status(thm)], ['54', '55'])).
% 23.64/23.81  thf('90', plain,
% 23.64/23.81      (![X0 : $i]:
% 23.64/23.81         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ (k1_tops_1 @ sk_A @ sk_C))
% 23.64/23.81           = (k4_xboole_0 @ X0 @ sk_C))),
% 23.64/23.81      inference('demod', [status(thm)], ['88', '89'])).
% 23.64/23.81  thf('91', plain,
% 23.64/23.81      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 23.64/23.81      inference('cnf', [status(esa)], [t36_xboole_1])).
% 23.64/23.81  thf('92', plain,
% 23.64/23.81      (![X3 : $i, X4 : $i, X5 : $i]:
% 23.64/23.81         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ X4 @ X5)))),
% 23.64/23.81      inference('cnf', [status(esa)], [t106_xboole_1])).
% 23.64/23.81  thf('93', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.64/23.81         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X1)),
% 23.64/23.81      inference('sup-', [status(thm)], ['91', '92'])).
% 23.64/23.81  thf('94', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.64/23.81         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X0))
% 23.64/23.81          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 23.64/23.81      inference('sup-', [status(thm)], ['61', '62'])).
% 23.64/23.81  thf('95', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.64/23.81         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1) @ 
% 23.64/23.81          (k4_xboole_0 @ X0 @ X1))),
% 23.64/23.81      inference('sup-', [status(thm)], ['93', '94'])).
% 23.64/23.81  thf('96', plain,
% 23.64/23.81      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 23.64/23.81      inference('cnf', [status(esa)], [t36_xboole_1])).
% 23.64/23.81  thf('97', plain,
% 23.64/23.81      (![X3 : $i, X4 : $i, X5 : $i]:
% 23.64/23.81         ((r1_xboole_0 @ X3 @ X5)
% 23.64/23.81          | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ X4 @ X5)))),
% 23.64/23.81      inference('cnf', [status(esa)], [t106_xboole_1])).
% 23.64/23.81  thf('98', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.64/23.81         (r1_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0)),
% 23.64/23.81      inference('sup-', [status(thm)], ['96', '97'])).
% 23.64/23.81  thf('99', plain,
% 23.64/23.81      (![X17 : $i, X18 : $i, X19 : $i]:
% 23.64/23.81         (~ (r1_tarski @ X17 @ X18)
% 23.64/23.81          | ~ (r1_xboole_0 @ X17 @ X19)
% 23.64/23.81          | (r1_tarski @ X17 @ (k4_xboole_0 @ X18 @ X19)))),
% 23.64/23.81      inference('cnf', [status(esa)], [t86_xboole_1])).
% 23.64/23.81  thf('100', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 23.64/23.81         ((r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1) @ 
% 23.64/23.81           (k4_xboole_0 @ X3 @ X0))
% 23.64/23.81          | ~ (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1) @ X3))),
% 23.64/23.81      inference('sup-', [status(thm)], ['98', '99'])).
% 23.64/23.81  thf('101', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.64/23.81         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ X0) @ 
% 23.64/23.81          (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 23.64/23.81      inference('sup-', [status(thm)], ['95', '100'])).
% 23.64/23.81  thf('102', plain,
% 23.64/23.81      (![X0 : $i, X2 : $i]:
% 23.64/23.81         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 23.64/23.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 23.64/23.81  thf('103', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.64/23.81         (~ (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ 
% 23.64/23.81             (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1))
% 23.64/23.81          | ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 23.64/23.81              = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)))),
% 23.64/23.81      inference('sup-', [status(thm)], ['101', '102'])).
% 23.64/23.81  thf('104', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.64/23.81         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ X0) @ 
% 23.64/23.81          (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 23.64/23.81      inference('sup-', [status(thm)], ['95', '100'])).
% 23.64/23.81  thf('105', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 23.64/23.81         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 23.64/23.81           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 23.64/23.81      inference('demod', [status(thm)], ['103', '104'])).
% 23.64/23.81  thf('106', plain,
% 23.64/23.81      (![X3 : $i, X4 : $i, X5 : $i]:
% 23.64/23.81         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ X4 @ X5)))),
% 23.64/23.81      inference('cnf', [status(esa)], [t106_xboole_1])).
% 23.64/23.81  thf('107', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 23.64/23.81         (~ (r1_tarski @ X3 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 23.64/23.81          | (r1_tarski @ X3 @ (k4_xboole_0 @ X2 @ X0)))),
% 23.64/23.81      inference('sup-', [status(thm)], ['105', '106'])).
% 23.64/23.81  thf('108', plain,
% 23.64/23.81      (![X0 : $i, X1 : $i]:
% 23.64/23.81         (~ (r1_tarski @ X1 @ (k4_xboole_0 @ X0 @ sk_C))
% 23.64/23.81          | (r1_tarski @ X1 @ (k4_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_C))))),
% 23.64/23.81      inference('sup-', [status(thm)], ['90', '107'])).
% 23.64/23.81  thf('109', plain,
% 23.64/23.81      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 23.64/23.81        (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 23.64/23.81      inference('sup-', [status(thm)], ['49', '108'])).
% 23.64/23.81  thf('110', plain, ($false), inference('demod', [status(thm)], ['22', '109'])).
% 23.64/23.81  
% 23.64/23.81  % SZS output end Refutation
% 23.64/23.81  
% 23.64/23.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
