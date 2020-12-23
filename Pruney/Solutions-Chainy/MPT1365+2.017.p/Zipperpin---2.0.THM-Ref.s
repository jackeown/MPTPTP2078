%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iqWRByfrd4

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:37 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 158 expanded)
%              Number of leaves         :   23 (  57 expanded)
%              Depth                    :   13
%              Number of atoms          :  666 (2047 expanded)
%              Number of equality atoms :    8 (  17 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
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

thf(fc4_tops_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( v4_pre_topc @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( v4_pre_topc @ C @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k3_xboole_0 @ B @ C ) @ A ) ) )).

thf('7',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v4_pre_topc @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( v4_pre_topc @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v4_pre_topc @ ( k3_xboole_0 @ X17 @ X19 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc4_tops_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v4_pre_topc @ X20 @ X21 )
      | ~ ( v2_compts_1 @ X20 @ X21 )
      | ~ ( v8_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('14',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','19'])).

thf('21',plain,
    ( ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v4_pre_topc @ X20 @ X21 )
      | ~ ( v2_compts_1 @ X20 @ X21 )
      | ~ ( v8_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('24',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_C @ sk_A )
    | ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v4_pre_topc @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['24','25','26','27','28'])).

thf('30',plain,(
    v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['21','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('38',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X6 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('42',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_subset_1 @ sk_C @ X0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','43'])).

thf('45',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ sk_C @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('48',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('52',plain,(
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

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_compts_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_C )
      | ~ ( v4_pre_topc @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('63',plain,(
    v2_compts_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['30','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['4','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iqWRByfrd4
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:28:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.61  % Solved by: fo/fo7.sh
% 0.42/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.61  % done 142 iterations in 0.103s
% 0.42/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.61  % SZS output start Refutation
% 0.42/0.61  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.42/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.61  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.42/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.42/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.42/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.42/0.61  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.42/0.61  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.42/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
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
% 0.42/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.42/0.61         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.42/0.61          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
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
% 0.42/0.61  thf(fc4_tops_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v4_pre_topc @ B @ A ) & 
% 0.42/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.42/0.61         ( v4_pre_topc @ C @ A ) & 
% 0.42/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.42/0.61       ( v4_pre_topc @ ( k3_xboole_0 @ B @ C ) @ A ) ))).
% 0.42/0.61  thf('7', plain,
% 0.42/0.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.42/0.61          | ~ (v4_pre_topc @ X17 @ X18)
% 0.42/0.61          | ~ (l1_pre_topc @ X18)
% 0.42/0.61          | ~ (v2_pre_topc @ X18)
% 0.42/0.61          | ~ (v4_pre_topc @ X19 @ X18)
% 0.42/0.61          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.42/0.61          | (v4_pre_topc @ (k3_xboole_0 @ X17 @ X19) @ X18))),
% 0.42/0.61      inference('cnf', [status(esa)], [fc4_tops_1])).
% 0.42/0.61  thf('8', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.42/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.42/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.42/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.42/0.61          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.42/0.61  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('11', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.42/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.42/0.61          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.42/0.61  thf('12', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(t16_compts_1, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.42/0.61       ( ![B:$i]:
% 0.42/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.61           ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) ) =>
% 0.42/0.61             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.42/0.61  thf('13', plain,
% 0.42/0.61      (![X20 : $i, X21 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.42/0.61          | (v4_pre_topc @ X20 @ X21)
% 0.42/0.61          | ~ (v2_compts_1 @ X20 @ X21)
% 0.42/0.61          | ~ (v8_pre_topc @ X21)
% 0.42/0.61          | ~ (l1_pre_topc @ X21)
% 0.42/0.61          | ~ (v2_pre_topc @ X21))),
% 0.42/0.61      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.42/0.61  thf('14', plain,
% 0.42/0.61      ((~ (v2_pre_topc @ sk_A)
% 0.42/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.42/0.61        | ~ (v8_pre_topc @ sk_A)
% 0.42/0.61        | ~ (v2_compts_1 @ sk_B @ sk_A)
% 0.42/0.61        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.42/0.61  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('17', plain, ((v8_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('18', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('19', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.42/0.61      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.42/0.61  thf('20', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.42/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)], ['11', '19'])).
% 0.42/0.61  thf('21', plain,
% 0.42/0.61      ((~ (v4_pre_topc @ sk_C @ sk_A)
% 0.42/0.61        | (v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['5', '20'])).
% 0.42/0.61  thf('22', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('23', plain,
% 0.42/0.61      (![X20 : $i, X21 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.42/0.61          | (v4_pre_topc @ X20 @ X21)
% 0.42/0.61          | ~ (v2_compts_1 @ X20 @ X21)
% 0.42/0.61          | ~ (v8_pre_topc @ X21)
% 0.42/0.61          | ~ (l1_pre_topc @ X21)
% 0.42/0.61          | ~ (v2_pre_topc @ X21))),
% 0.42/0.61      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.42/0.61  thf('24', plain,
% 0.42/0.61      ((~ (v2_pre_topc @ sk_A)
% 0.42/0.61        | ~ (l1_pre_topc @ sk_A)
% 0.42/0.61        | ~ (v8_pre_topc @ sk_A)
% 0.42/0.61        | ~ (v2_compts_1 @ sk_C @ sk_A)
% 0.42/0.61        | (v4_pre_topc @ sk_C @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.42/0.61  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('27', plain, ((v8_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('28', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('29', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.42/0.61      inference('demod', [status(thm)], ['24', '25', '26', '27', '28'])).
% 0.42/0.61  thf('30', plain, ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.42/0.61      inference('demod', [status(thm)], ['21', '29'])).
% 0.42/0.61  thf('31', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(t3_subset, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.42/0.61  thf('32', plain,
% 0.42/0.61      (![X14 : $i, X15 : $i]:
% 0.42/0.61         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.61  thf('33', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.42/0.61  thf(d10_xboole_0, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.42/0.61  thf('34', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.42/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.42/0.61  thf('35', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.42/0.61      inference('simplify', [status(thm)], ['34'])).
% 0.42/0.61  thf('36', plain,
% 0.42/0.61      (![X14 : $i, X16 : $i]:
% 0.42/0.61         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.42/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.61  thf('37', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['35', '36'])).
% 0.42/0.61  thf(dt_k9_subset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.61       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.42/0.61  thf('38', plain,
% 0.42/0.61      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.42/0.61         ((m1_subset_1 @ (k9_subset_1 @ X6 @ X7 @ X8) @ (k1_zfmisc_1 @ X6))
% 0.42/0.61          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X6)))),
% 0.42/0.61      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.42/0.61  thf('39', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['37', '38'])).
% 0.42/0.61  thf('40', plain,
% 0.42/0.61      (![X14 : $i, X15 : $i]:
% 0.42/0.61         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.61  thf('41', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X0)),
% 0.42/0.61      inference('sup-', [status(thm)], ['39', '40'])).
% 0.42/0.61  thf(t1_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.42/0.61       ( r1_tarski @ A @ C ) ))).
% 0.42/0.61  thf('42', plain,
% 0.42/0.61      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.42/0.61         (~ (r1_tarski @ X3 @ X4)
% 0.42/0.61          | ~ (r1_tarski @ X4 @ X5)
% 0.42/0.61          | (r1_tarski @ X3 @ X5))),
% 0.42/0.61      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.42/0.61  thf('43', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         ((r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X2)
% 0.42/0.61          | ~ (r1_tarski @ X0 @ X2))),
% 0.42/0.61      inference('sup-', [status(thm)], ['41', '42'])).
% 0.42/0.61  thf('44', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (r1_tarski @ (k9_subset_1 @ sk_C @ X0 @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['33', '43'])).
% 0.42/0.61  thf('45', plain,
% 0.42/0.61      (![X14 : $i, X16 : $i]:
% 0.42/0.61         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.42/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.61  thf('46', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (m1_subset_1 @ (k9_subset_1 @ sk_C @ X0 @ sk_C) @ 
% 0.42/0.61          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['44', '45'])).
% 0.42/0.61  thf('47', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['35', '36'])).
% 0.42/0.61  thf('48', plain,
% 0.42/0.61      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.42/0.61         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.42/0.61          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.42/0.61      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.42/0.61  thf('49', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['47', '48'])).
% 0.42/0.61  thf('50', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 0.42/0.61          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('demod', [status(thm)], ['46', '49'])).
% 0.42/0.61  thf('51', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
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
% 0.42/0.61  thf('52', plain,
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
% 0.42/0.61  thf('53', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (v2_pre_topc @ sk_A)
% 0.42/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.42/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61          | (v2_compts_1 @ X0 @ sk_A)
% 0.42/0.61          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.42/0.61          | ~ (r1_tarski @ X0 @ sk_C)
% 0.42/0.61          | ~ (v2_compts_1 @ sk_C @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['51', '52'])).
% 0.42/0.61  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('56', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('57', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61          | (v2_compts_1 @ X0 @ sk_A)
% 0.42/0.61          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.42/0.61          | ~ (r1_tarski @ X0 @ sk_C))),
% 0.42/0.61      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.42/0.61  thf('58', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ sk_C)
% 0.42/0.61          | ~ (v4_pre_topc @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A)
% 0.42/0.61          | (v2_compts_1 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A))),
% 0.46/0.61      inference('sup-', [status(thm)], ['50', '57'])).
% 0.46/0.61  thf('59', plain,
% 0.46/0.61      (![X0 : $i, X1 : $i]:
% 0.46/0.61         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.46/0.61      inference('sup-', [status(thm)], ['47', '48'])).
% 0.46/0.61  thf('60', plain,
% 0.46/0.61      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X0)),
% 0.46/0.61      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.61  thf('61', plain,
% 0.46/0.61      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.46/0.61      inference('sup+', [status(thm)], ['59', '60'])).
% 0.46/0.61  thf('62', plain,
% 0.46/0.61      (![X0 : $i]:
% 0.46/0.61         (~ (v4_pre_topc @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A)
% 0.46/0.61          | (v2_compts_1 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A))),
% 0.46/0.61      inference('demod', [status(thm)], ['58', '61'])).
% 0.46/0.61  thf('63', plain, ((v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.46/0.61      inference('sup-', [status(thm)], ['30', '62'])).
% 0.46/0.61  thf('64', plain, ($false), inference('demod', [status(thm)], ['4', '63'])).
% 0.46/0.61  
% 0.46/0.61  % SZS output end Refutation
% 0.46/0.61  
% 0.46/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
