%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6NMQzafOeU

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:38 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 148 expanded)
%              Number of leaves         :   28 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  686 (2058 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(t20_compts_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v8_pre_topc @ A )
                  & ( v2_compts_1 @ B @ A )
                  & ( v2_compts_1 @ C @ A ) )
               => ( v2_compts_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v8_pre_topc @ A )
                    & ( v2_compts_1 @ B @ A )
                    & ( v2_compts_1 @ C @ A ) )
                 => ( v2_compts_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_compts_1])).

thf('0',plain,(
    ~ ( v2_compts_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X14 @ X12 @ X13 )
        = ( k3_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_compts_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v4_pre_topc @ B @ A )
                  & ( v4_pre_topc @ C @ A ) )
               => ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v4_pre_topc @ X20 @ X21 )
      | ~ ( v4_pre_topc @ X22 @ X21 )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 @ X22 ) @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_tops_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t16_compts_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v8_pre_topc @ A )
              & ( v2_compts_1 @ B @ A ) )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v4_pre_topc @ X23 @ X24 )
      | ~ ( v2_compts_1 @ X23 @ X24 )
      | ~ ( v8_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('13',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['13','14','15','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10','18'])).

thf('20',plain,
    ( ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v4_pre_topc @ X23 @ X24 )
      | ~ ( v2_compts_1 @ X23 @ X24 )
      | ~ ( v8_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('23',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_C @ sk_A )
    | ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v4_pre_topc @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('30',plain,(
    v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['20','28','29'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X7 @ X6 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('36',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k7_subset_1 @ X10 @ X9 @ X11 )
        = ( k4_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['31','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_compts_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v2_compts_1 @ B @ A )
                  & ( r1_tarski @ C @ B )
                  & ( v4_pre_topc @ C @ A ) )
               => ( v2_compts_1 @ C @ A ) ) ) ) ) )).

thf('41',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_compts_1 @ X25 @ X26 )
      | ~ ( r1_tarski @ X27 @ X25 )
      | ~ ( v4_pre_topc @ X27 @ X26 )
      | ( v2_compts_1 @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t18_compts_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_compts_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ~ ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('49',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X5 ) @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('50',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('51',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( ( k7_subset_1 @ X10 @ X9 @ X11 )
        = ( k4_xboole_0 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('55',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X7 @ X6 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ X0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['48','57'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('59',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','60'])).

thf('62',plain,(
    v2_compts_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['30','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['4','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6NMQzafOeU
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:04:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.55  % Solved by: fo/fo7.sh
% 0.19/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.55  % done 161 iterations in 0.103s
% 0.19/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.55  % SZS output start Refutation
% 0.19/0.55  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.19/0.55  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.19/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.55  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.19/0.55  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.19/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.55  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.19/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.55  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.19/0.55  thf(t20_compts_1, conjecture,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.55       ( ![B:$i]:
% 0.19/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.55           ( ![C:$i]:
% 0.19/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.55               ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.19/0.55                   ( v2_compts_1 @ C @ A ) ) =>
% 0.19/0.55                 ( v2_compts_1 @
% 0.19/0.55                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.19/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.55    (~( ![A:$i]:
% 0.19/0.55        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.55          ( ![B:$i]:
% 0.19/0.55            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.55              ( ![C:$i]:
% 0.19/0.55                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.55                  ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.19/0.55                      ( v2_compts_1 @ C @ A ) ) =>
% 0.19/0.55                    ( v2_compts_1 @
% 0.19/0.55                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.19/0.55    inference('cnf.neg', [status(esa)], [t20_compts_1])).
% 0.19/0.55  thf('0', plain,
% 0.19/0.55      (~ (v2_compts_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.19/0.55          sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('1', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(redefinition_k9_subset_1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.55       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.19/0.55  thf('2', plain,
% 0.19/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.55         (((k9_subset_1 @ X14 @ X12 @ X13) = (k3_xboole_0 @ X12 @ X13))
% 0.19/0.55          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.19/0.55      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.19/0.55  thf('3', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.19/0.55           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.19/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.55  thf('4', plain, (~ (v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.19/0.55      inference('demod', [status(thm)], ['0', '3'])).
% 0.19/0.55  thf('5', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('6', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(t35_tops_1, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.55       ( ![B:$i]:
% 0.19/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.55           ( ![C:$i]:
% 0.19/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.55               ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 0.19/0.55                 ( v4_pre_topc @
% 0.19/0.55                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.19/0.55  thf('7', plain,
% 0.19/0.55      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.19/0.55          | ~ (v4_pre_topc @ X20 @ X21)
% 0.19/0.55          | ~ (v4_pre_topc @ X22 @ X21)
% 0.19/0.55          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ X21) @ X20 @ X22) @ 
% 0.19/0.55             X21)
% 0.19/0.55          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.19/0.55          | ~ (l1_pre_topc @ X21)
% 0.19/0.55          | ~ (v2_pre_topc @ X21))),
% 0.19/0.55      inference('cnf', [status(esa)], [t35_tops_1])).
% 0.19/0.55  thf('8', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (~ (v2_pre_topc @ sk_A)
% 0.19/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.55          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.19/0.55             sk_A)
% 0.19/0.55          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.19/0.55          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.19/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.55  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('11', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(t16_compts_1, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.55       ( ![B:$i]:
% 0.19/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.55           ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) ) =>
% 0.19/0.55             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.19/0.55  thf('12', plain,
% 0.19/0.55      (![X23 : $i, X24 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.19/0.55          | (v4_pre_topc @ X23 @ X24)
% 0.19/0.55          | ~ (v2_compts_1 @ X23 @ X24)
% 0.19/0.55          | ~ (v8_pre_topc @ X24)
% 0.19/0.55          | ~ (l1_pre_topc @ X24)
% 0.19/0.55          | ~ (v2_pre_topc @ X24))),
% 0.19/0.55      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.19/0.55  thf('13', plain,
% 0.19/0.55      ((~ (v2_pre_topc @ sk_A)
% 0.19/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.55        | ~ (v8_pre_topc @ sk_A)
% 0.19/0.55        | ~ (v2_compts_1 @ sk_B @ sk_A)
% 0.19/0.55        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.19/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.55  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('16', plain, ((v8_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('17', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('18', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.19/0.55      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.19/0.55  thf('19', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.55          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.19/0.55             sk_A)
% 0.19/0.55          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.19/0.55      inference('demod', [status(thm)], ['8', '9', '10', '18'])).
% 0.19/0.55  thf('20', plain,
% 0.19/0.55      ((~ (v4_pre_topc @ sk_C @ sk_A)
% 0.19/0.55        | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.19/0.55           sk_A))),
% 0.19/0.55      inference('sup-', [status(thm)], ['5', '19'])).
% 0.19/0.55  thf('21', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('22', plain,
% 0.19/0.55      (![X23 : $i, X24 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.19/0.55          | (v4_pre_topc @ X23 @ X24)
% 0.19/0.55          | ~ (v2_compts_1 @ X23 @ X24)
% 0.19/0.55          | ~ (v8_pre_topc @ X24)
% 0.19/0.55          | ~ (l1_pre_topc @ X24)
% 0.19/0.55          | ~ (v2_pre_topc @ X24))),
% 0.19/0.55      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.19/0.55  thf('23', plain,
% 0.19/0.55      ((~ (v2_pre_topc @ sk_A)
% 0.19/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.19/0.55        | ~ (v8_pre_topc @ sk_A)
% 0.19/0.55        | ~ (v2_compts_1 @ sk_C @ sk_A)
% 0.19/0.55        | (v4_pre_topc @ sk_C @ sk_A))),
% 0.19/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.55  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('26', plain, ((v8_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('27', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('28', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.19/0.55      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.19/0.55  thf('29', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.19/0.55           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.19/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.55  thf('30', plain, ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.19/0.55      inference('demod', [status(thm)], ['20', '28', '29'])).
% 0.19/0.55  thf(t48_xboole_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.19/0.55  thf('31', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.19/0.55           = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.19/0.55  thf('32', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(dt_k7_subset_1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.55       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.55  thf('33', plain,
% 0.19/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.19/0.55          | (m1_subset_1 @ (k7_subset_1 @ X7 @ X6 @ X8) @ (k1_zfmisc_1 @ X7)))),
% 0.19/0.55      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 0.19/0.55  thf('34', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.19/0.55          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['32', '33'])).
% 0.19/0.55  thf('35', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(redefinition_k7_subset_1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.55       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.19/0.55  thf('36', plain,
% 0.19/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.19/0.55          | ((k7_subset_1 @ X10 @ X9 @ X11) = (k4_xboole_0 @ X9 @ X11)))),
% 0.19/0.55      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.19/0.55  thf('37', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.19/0.55           = (k4_xboole_0 @ sk_B @ X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.55  thf('38', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.19/0.55          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.55      inference('demod', [status(thm)], ['34', '37'])).
% 0.19/0.55  thf('39', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 0.19/0.55          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.55      inference('sup+', [status(thm)], ['31', '38'])).
% 0.19/0.55  thf('40', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(t18_compts_1, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.55       ( ![B:$i]:
% 0.19/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.55           ( ![C:$i]:
% 0.19/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.55               ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 0.19/0.55                   ( v4_pre_topc @ C @ A ) ) =>
% 0.19/0.55                 ( v2_compts_1 @ C @ A ) ) ) ) ) ) ))).
% 0.19/0.55  thf('41', plain,
% 0.19/0.55      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.19/0.55          | ~ (v2_compts_1 @ X25 @ X26)
% 0.19/0.55          | ~ (r1_tarski @ X27 @ X25)
% 0.19/0.55          | ~ (v4_pre_topc @ X27 @ X26)
% 0.19/0.55          | (v2_compts_1 @ X27 @ X26)
% 0.19/0.55          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.19/0.55          | ~ (l1_pre_topc @ X26)
% 0.19/0.55          | ~ (v2_pre_topc @ X26))),
% 0.19/0.55      inference('cnf', [status(esa)], [t18_compts_1])).
% 0.19/0.55  thf('42', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (~ (v2_pre_topc @ sk_A)
% 0.19/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.55          | (v2_compts_1 @ X0 @ sk_A)
% 0.19/0.55          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.19/0.55          | ~ (r1_tarski @ X0 @ sk_B)
% 0.19/0.55          | ~ (v2_compts_1 @ sk_B @ sk_A))),
% 0.19/0.55      inference('sup-', [status(thm)], ['40', '41'])).
% 0.19/0.55  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('45', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('46', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.55          | (v2_compts_1 @ X0 @ sk_A)
% 0.19/0.55          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.19/0.55          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.19/0.55      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.19/0.55  thf('47', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ sk_B)
% 0.19/0.55          | ~ (v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.19/0.55          | (v2_compts_1 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.19/0.55      inference('sup-', [status(thm)], ['39', '46'])).
% 0.19/0.55  thf('48', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.19/0.55           = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.19/0.55  thf(dt_k2_subset_1, axiom,
% 0.19/0.55    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.55  thf('49', plain,
% 0.19/0.55      (![X5 : $i]: (m1_subset_1 @ (k2_subset_1 @ X5) @ (k1_zfmisc_1 @ X5))),
% 0.19/0.55      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.19/0.55  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.19/0.55  thf('50', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.19/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.19/0.55  thf('51', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.19/0.55      inference('demod', [status(thm)], ['49', '50'])).
% 0.19/0.55  thf('52', plain,
% 0.19/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.19/0.55          | ((k7_subset_1 @ X10 @ X9 @ X11) = (k4_xboole_0 @ X9 @ X11)))),
% 0.19/0.55      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.19/0.55  thf('53', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.19/0.55      inference('sup-', [status(thm)], ['51', '52'])).
% 0.19/0.55  thf('54', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 0.19/0.55      inference('demod', [status(thm)], ['49', '50'])).
% 0.19/0.55  thf('55', plain,
% 0.19/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.19/0.55          | (m1_subset_1 @ (k7_subset_1 @ X7 @ X6 @ X8) @ (k1_zfmisc_1 @ X7)))),
% 0.19/0.55      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 0.19/0.55  thf('56', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         (m1_subset_1 @ (k7_subset_1 @ X0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['54', '55'])).
% 0.19/0.55  thf('57', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         (m1_subset_1 @ (k4_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.19/0.55      inference('sup+', [status(thm)], ['53', '56'])).
% 0.19/0.55  thf('58', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.19/0.55      inference('sup+', [status(thm)], ['48', '57'])).
% 0.19/0.55  thf(t3_subset, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.55  thf('59', plain,
% 0.19/0.55      (![X17 : $i, X18 : $i]:
% 0.19/0.55         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.55  thf('60', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.19/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.19/0.55  thf('61', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (~ (v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.19/0.55          | (v2_compts_1 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A))),
% 0.19/0.55      inference('demod', [status(thm)], ['47', '60'])).
% 0.19/0.55  thf('62', plain, ((v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.19/0.55      inference('sup-', [status(thm)], ['30', '61'])).
% 0.19/0.55  thf('63', plain, ($false), inference('demod', [status(thm)], ['4', '62'])).
% 0.19/0.55  
% 0.19/0.55  % SZS output end Refutation
% 0.19/0.55  
% 0.19/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
