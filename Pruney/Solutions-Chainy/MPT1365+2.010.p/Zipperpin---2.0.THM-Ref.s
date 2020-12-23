%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZNX8qRHid5

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:36 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 173 expanded)
%              Number of leaves         :   27 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  846 (2775 expanded)
%              Number of equality atoms :   12 (  19 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_subset_1 @ X16 @ X14 @ X15 )
        = ( k3_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v4_pre_topc @ X17 @ X18 )
      | ~ ( v4_pre_topc @ X19 @ X18 )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 @ X19 ) @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v4_pre_topc @ X20 @ X21 )
      | ~ ( v2_compts_1 @ X20 @ X21 )
      | ~ ( v8_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v4_pre_topc @ X20 @ X21 )
      | ~ ( v2_compts_1 @ X20 @ X21 )
      | ~ ( v8_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
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

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('38',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X6 @ X5 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('43',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) )
      | ( ( k4_subset_1 @ X12 @ X11 @ X13 )
        = ( k2_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k2_xboole_0 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','45'])).

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

thf('47',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v2_compts_1 @ X22 @ X23 )
      | ~ ( r1_tarski @ X24 @ X22 )
      | ~ ( v4_pre_topc @ X24 @ X23 )
      | ( v2_compts_1 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t18_compts_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_C @ sk_B ) )
      | ~ ( v2_compts_1 @ ( k2_xboole_0 @ sk_C @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_C @ sk_B ) )
      | ~ ( v2_compts_1 @ ( k2_xboole_0 @ sk_C @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t19_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v2_compts_1 @ B @ A )
                  & ( v2_compts_1 @ C @ A ) )
               => ( v2_compts_1 @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf('54',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_compts_1 @ X25 @ X26 )
      | ~ ( v2_compts_1 @ X27 @ X26 )
      | ( v2_compts_1 @ ( k4_subset_1 @ ( u1_struct_0 @ X26 ) @ X25 @ X27 ) @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t19_compts_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v2_compts_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) @ sk_A )
      | ~ ( v2_compts_1 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ( v2_compts_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['52','58'])).

thf('60',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_B )
    = ( k2_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('62',plain,(
    v2_compts_1 @ ( k2_xboole_0 @ sk_C @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_C @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['51','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k2_xboole_0 @ sk_C @ sk_B ) )
      | ~ ( v4_pre_topc @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','63'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t29_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) )).

thf('66',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ ( k2_xboole_0 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t29_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,(
    v2_compts_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['30','68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['4','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZNX8qRHid5
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:25:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.61  % Solved by: fo/fo7.sh
% 0.42/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.61  % done 232 iterations in 0.155s
% 0.42/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.61  % SZS output start Refutation
% 0.42/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.61  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.42/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.61  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.42/0.61  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.42/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.42/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.42/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.42/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.42/0.61  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.42/0.61  thf(t20_compts_1, conjecture,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.61       ( ![B:$i]:
% 0.42/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.61           ( ![C:$i]:
% 0.42/0.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.61               ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.42/0.61                   ( v2_compts_1 @ C @ A ) ) =>
% 0.42/0.61                 ( v2_compts_1 @
% 0.42/0.61                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.42/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.61    (~( ![A:$i]:
% 0.42/0.61        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.61          ( ![B:$i]:
% 0.42/0.61            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.61              ( ![C:$i]:
% 0.42/0.61                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.61                  ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.42/0.61                      ( v2_compts_1 @ C @ A ) ) =>
% 0.42/0.61                    ( v2_compts_1 @
% 0.42/0.61                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.42/0.61    inference('cnf.neg', [status(esa)], [t20_compts_1])).
% 0.42/0.61  thf('0', plain,
% 0.42/0.61      (~ (v2_compts_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.42/0.61          sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('1', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(redefinition_k9_subset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.61       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.42/0.61  thf('2', plain,
% 0.42/0.61      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.42/0.61         (((k9_subset_1 @ X16 @ X14 @ X15) = (k3_xboole_0 @ X14 @ X15))
% 0.42/0.61          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.42/0.61      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.42/0.61  thf('3', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.42/0.61           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.42/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.61  thf('4', plain, (~ (v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.42/0.61      inference('demod', [status(thm)], ['0', '3'])).
% 0.42/0.61  thf('5', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('6', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(t35_tops_1, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.61       ( ![B:$i]:
% 0.42/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.61           ( ![C:$i]:
% 0.42/0.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.61               ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 0.42/0.61                 ( v4_pre_topc @
% 0.42/0.61                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.42/0.61  thf('7', plain,
% 0.42/0.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.42/0.61          | ~ (v4_pre_topc @ X17 @ X18)
% 0.42/0.61          | ~ (v4_pre_topc @ X19 @ X18)
% 0.42/0.61          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ X18) @ X17 @ X19) @ 
% 0.42/0.61             X18)
% 0.42/0.61          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.42/0.61          | ~ (l1_pre_topc @ X18)
% 0.42/0.61          | ~ (v2_pre_topc @ X18))),
% 0.42/0.61      inference('cnf', [status(esa)], [t35_tops_1])).
% 0.42/0.61  thf('8', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (v2_pre_topc @ sk_A)
% 0.42/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.42/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.42/0.61             sk_A)
% 0.42/0.61          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.42/0.61          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.42/0.61  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('11', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(t16_compts_1, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.61       ( ![B:$i]:
% 0.42/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.61           ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) ) =>
% 0.42/0.61             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.42/0.61  thf('12', plain,
% 0.42/0.61      (![X20 : $i, X21 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.42/0.61          | (v4_pre_topc @ X20 @ X21)
% 0.42/0.61          | ~ (v2_compts_1 @ X20 @ X21)
% 0.42/0.61          | ~ (v8_pre_topc @ X21)
% 0.42/0.61          | ~ (l1_pre_topc @ X21)
% 0.42/0.61          | ~ (v2_pre_topc @ X21))),
% 0.42/0.61      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.42/0.61  thf('13', plain,
% 0.42/0.61      ((~ (v2_pre_topc @ sk_A)
% 0.42/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.42/0.61        | ~ (v8_pre_topc @ sk_A)
% 0.42/0.61        | ~ (v2_compts_1 @ sk_B @ sk_A)
% 0.42/0.61        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.42/0.61  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('16', plain, ((v8_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('17', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('18', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.42/0.61      inference('demod', [status(thm)], ['13', '14', '15', '16', '17'])).
% 0.42/0.61  thf('19', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.42/0.61             sk_A)
% 0.42/0.61          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)], ['8', '9', '10', '18'])).
% 0.42/0.61  thf('20', plain,
% 0.42/0.61      ((~ (v4_pre_topc @ sk_C @ sk_A)
% 0.42/0.61        | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.42/0.61           sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['5', '19'])).
% 0.42/0.61  thf('21', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('22', plain,
% 0.42/0.61      (![X20 : $i, X21 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.42/0.61          | (v4_pre_topc @ X20 @ X21)
% 0.42/0.61          | ~ (v2_compts_1 @ X20 @ X21)
% 0.42/0.61          | ~ (v8_pre_topc @ X21)
% 0.42/0.61          | ~ (l1_pre_topc @ X21)
% 0.42/0.61          | ~ (v2_pre_topc @ X21))),
% 0.42/0.61      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.42/0.61  thf('23', plain,
% 0.42/0.61      ((~ (v2_pre_topc @ sk_A)
% 0.42/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.42/0.61        | ~ (v8_pre_topc @ sk_A)
% 0.42/0.61        | ~ (v2_compts_1 @ sk_C @ sk_A)
% 0.42/0.61        | (v4_pre_topc @ sk_C @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['21', '22'])).
% 0.42/0.61  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('26', plain, ((v8_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('27', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('28', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.42/0.61      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.42/0.61  thf('29', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.42/0.61           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.42/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.61  thf('30', plain, ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.42/0.61      inference('demod', [status(thm)], ['20', '28', '29'])).
% 0.42/0.61  thf('31', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(dt_k9_subset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.61       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.42/0.61  thf('32', plain,
% 0.42/0.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.42/0.61         ((m1_subset_1 @ (k9_subset_1 @ X8 @ X9 @ X10) @ (k1_zfmisc_1 @ X8))
% 0.42/0.61          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X8)))),
% 0.42/0.61      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.42/0.61  thf('33', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ 
% 0.42/0.61          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.42/0.61  thf('34', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.42/0.61           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.42/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.61  thf('35', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 0.42/0.61          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('demod', [status(thm)], ['33', '34'])).
% 0.42/0.61  thf('36', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('37', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(dt_k4_subset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.42/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.61       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.42/0.61  thf('38', plain,
% 0.42/0.61      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.42/0.61          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6))
% 0.42/0.61          | (m1_subset_1 @ (k4_subset_1 @ X6 @ X5 @ X7) @ (k1_zfmisc_1 @ X6)))),
% 0.42/0.61      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.42/0.61  thf('39', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0) @ 
% 0.42/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['37', '38'])).
% 0.42/0.61  thf('40', plain,
% 0.42/0.61      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_B) @ 
% 0.42/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['36', '39'])).
% 0.42/0.61  thf('41', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('42', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(redefinition_k4_subset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.42/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.61       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.42/0.61  thf('43', plain,
% 0.42/0.61      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.42/0.61          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12))
% 0.42/0.61          | ((k4_subset_1 @ X12 @ X11 @ X13) = (k2_xboole_0 @ X11 @ X13)))),
% 0.42/0.61      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.42/0.61  thf('44', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)
% 0.42/0.61            = (k2_xboole_0 @ sk_C @ X0))
% 0.42/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['42', '43'])).
% 0.42/0.61  thf('45', plain,
% 0.42/0.61      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_B)
% 0.42/0.61         = (k2_xboole_0 @ sk_C @ sk_B))),
% 0.42/0.61      inference('sup-', [status(thm)], ['41', '44'])).
% 0.42/0.61  thf('46', plain,
% 0.42/0.61      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_B) @ 
% 0.42/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('demod', [status(thm)], ['40', '45'])).
% 0.42/0.61  thf(t18_compts_1, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.61       ( ![B:$i]:
% 0.42/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.61           ( ![C:$i]:
% 0.42/0.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.61               ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 0.42/0.61                   ( v4_pre_topc @ C @ A ) ) =>
% 0.42/0.61                 ( v2_compts_1 @ C @ A ) ) ) ) ) ) ))).
% 0.42/0.61  thf('47', plain,
% 0.42/0.61      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.42/0.61          | ~ (v2_compts_1 @ X22 @ X23)
% 0.42/0.61          | ~ (r1_tarski @ X24 @ X22)
% 0.42/0.61          | ~ (v4_pre_topc @ X24 @ X23)
% 0.42/0.61          | (v2_compts_1 @ X24 @ X23)
% 0.42/0.61          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.42/0.61          | ~ (l1_pre_topc @ X23)
% 0.42/0.61          | ~ (v2_pre_topc @ X23))),
% 0.42/0.61      inference('cnf', [status(esa)], [t18_compts_1])).
% 0.42/0.61  thf('48', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (v2_pre_topc @ sk_A)
% 0.42/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.42/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61          | (v2_compts_1 @ X0 @ sk_A)
% 0.42/0.61          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.42/0.61          | ~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_C @ sk_B))
% 0.42/0.61          | ~ (v2_compts_1 @ (k2_xboole_0 @ sk_C @ sk_B) @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['46', '47'])).
% 0.42/0.61  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('51', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61          | (v2_compts_1 @ X0 @ sk_A)
% 0.42/0.61          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.42/0.61          | ~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_C @ sk_B))
% 0.42/0.61          | ~ (v2_compts_1 @ (k2_xboole_0 @ sk_C @ sk_B) @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.42/0.61  thf('52', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('53', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(t19_compts_1, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( l1_pre_topc @ A ) =>
% 0.42/0.61       ( ![B:$i]:
% 0.42/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.61           ( ![C:$i]:
% 0.42/0.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.61               ( ( ( v2_compts_1 @ B @ A ) & ( v2_compts_1 @ C @ A ) ) =>
% 0.42/0.61                 ( v2_compts_1 @
% 0.42/0.61                   ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.42/0.61  thf('54', plain,
% 0.42/0.61      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.42/0.61          | ~ (v2_compts_1 @ X25 @ X26)
% 0.42/0.61          | ~ (v2_compts_1 @ X27 @ X26)
% 0.42/0.61          | (v2_compts_1 @ (k4_subset_1 @ (u1_struct_0 @ X26) @ X25 @ X27) @ 
% 0.42/0.61             X26)
% 0.42/0.61          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.42/0.61          | ~ (l1_pre_topc @ X26))),
% 0.42/0.61      inference('cnf', [status(esa)], [t19_compts_1])).
% 0.42/0.61  thf('55', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (l1_pre_topc @ sk_A)
% 0.42/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61          | (v2_compts_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0) @ 
% 0.42/0.61             sk_A)
% 0.42/0.61          | ~ (v2_compts_1 @ X0 @ sk_A)
% 0.42/0.61          | ~ (v2_compts_1 @ sk_C @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['53', '54'])).
% 0.42/0.61  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('57', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('58', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61          | (v2_compts_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0) @ 
% 0.42/0.61             sk_A)
% 0.42/0.61          | ~ (v2_compts_1 @ X0 @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.42/0.61  thf('59', plain,
% 0.42/0.61      ((~ (v2_compts_1 @ sk_B @ sk_A)
% 0.42/0.61        | (v2_compts_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_B) @ 
% 0.42/0.61           sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['52', '58'])).
% 0.42/0.61  thf('60', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('61', plain,
% 0.42/0.61      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_B)
% 0.42/0.61         = (k2_xboole_0 @ sk_C @ sk_B))),
% 0.42/0.61      inference('sup-', [status(thm)], ['41', '44'])).
% 0.42/0.61  thf('62', plain, ((v2_compts_1 @ (k2_xboole_0 @ sk_C @ sk_B) @ sk_A)),
% 0.42/0.61      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.42/0.61  thf('63', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61          | (v2_compts_1 @ X0 @ sk_A)
% 0.42/0.61          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.42/0.61          | ~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_C @ sk_B)))),
% 0.42/0.61      inference('demod', [status(thm)], ['51', '62'])).
% 0.42/0.61  thf('64', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 0.42/0.61             (k2_xboole_0 @ sk_C @ sk_B))
% 0.42/0.61          | ~ (v4_pre_topc @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A)
% 0.42/0.61          | (v2_compts_1 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['35', '63'])).
% 0.42/0.61  thf(commutativity_k3_xboole_0, axiom,
% 0.42/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.42/0.61  thf('65', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.42/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.42/0.61  thf(t29_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ))).
% 0.42/0.61  thf('66', plain,
% 0.42/0.61      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.42/0.61         (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ (k2_xboole_0 @ X2 @ X4))),
% 0.42/0.61      inference('cnf', [status(esa)], [t29_xboole_1])).
% 0.42/0.61  thf('67', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2))),
% 0.42/0.61      inference('sup+', [status(thm)], ['65', '66'])).
% 0.42/0.61  thf('68', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (v4_pre_topc @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A)
% 0.42/0.61          | (v2_compts_1 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)], ['64', '67'])).
% 0.42/0.61  thf('69', plain, ((v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.42/0.61      inference('sup-', [status(thm)], ['30', '68'])).
% 0.42/0.61  thf('70', plain, ($false), inference('demod', [status(thm)], ['4', '69'])).
% 0.42/0.61  
% 0.42/0.61  % SZS output end Refutation
% 0.42/0.61  
% 0.42/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
