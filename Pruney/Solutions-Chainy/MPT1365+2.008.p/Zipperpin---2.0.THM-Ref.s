%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C9zdAkhspV

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:36 EST 2020

% Result     : Theorem 0.33s
% Output     : Refutation 0.33s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 143 expanded)
%              Number of leaves         :   23 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :  682 (2159 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k9_subset_1 @ X4 @ X6 @ X5 )
        = ( k9_subset_1 @ X4 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v2_compts_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v4_pre_topc @ X13 @ X14 )
      | ~ ( v4_pre_topc @ X15 @ X14 )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 @ X15 ) @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t35_tops_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k9_subset_1 @ X4 @ X6 @ X5 )
        = ( k9_subset_1 @ X4 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v4_pre_topc @ X16 @ X17 )
      | ~ ( v2_compts_1 @ X16 @ X17 )
      | ~ ( v8_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('24',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
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
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['24','25','26','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','21','29'])).

thf('31',plain,
    ( ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ( v4_pre_topc @ ( k3_xboole_0 @ sk_C @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['11','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v4_pre_topc @ X16 @ X17 )
      | ~ ( v2_compts_1 @ X16 @ X17 )
      | ~ ( v8_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('34',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_C @ sk_A )
    | ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v4_pre_topc @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['34','35','36','37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('41',plain,(
    v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['31','39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('43',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X7 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,(
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

thf('50',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_compts_1 @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ X18 )
      | ~ ( v4_pre_topc @ X20 @ X19 )
      | ( v2_compts_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t18_compts_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_compts_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_C )
      | ~ ( v4_pre_topc @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('58',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X3 ) @ X2 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    v2_compts_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['41','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['10','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C9zdAkhspV
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.33/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.33/0.52  % Solved by: fo/fo7.sh
% 0.33/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.33/0.52  % done 136 iterations in 0.073s
% 0.33/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.33/0.52  % SZS output start Refutation
% 0.33/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.33/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.33/0.52  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.33/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.33/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.33/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.33/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.33/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.33/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.33/0.52  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.33/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.33/0.52  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.33/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.33/0.52  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.33/0.52  thf(t20_compts_1, conjecture,
% 0.33/0.52    (![A:$i]:
% 0.33/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.33/0.52       ( ![B:$i]:
% 0.33/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.33/0.52           ( ![C:$i]:
% 0.33/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.33/0.52               ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.33/0.52                   ( v2_compts_1 @ C @ A ) ) =>
% 0.33/0.52                 ( v2_compts_1 @
% 0.33/0.52                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.33/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.33/0.52    (~( ![A:$i]:
% 0.33/0.52        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.33/0.52          ( ![B:$i]:
% 0.33/0.52            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.33/0.52              ( ![C:$i]:
% 0.33/0.52                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.33/0.52                  ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.33/0.52                      ( v2_compts_1 @ C @ A ) ) =>
% 0.33/0.52                    ( v2_compts_1 @
% 0.33/0.52                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.33/0.52    inference('cnf.neg', [status(esa)], [t20_compts_1])).
% 0.33/0.52  thf('0', plain,
% 0.33/0.52      (~ (v2_compts_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.33/0.52          sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('1', plain,
% 0.33/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf(commutativity_k9_subset_1, axiom,
% 0.33/0.52    (![A:$i,B:$i,C:$i]:
% 0.33/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.33/0.52       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.33/0.52  thf('2', plain,
% 0.33/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.33/0.52         (((k9_subset_1 @ X4 @ X6 @ X5) = (k9_subset_1 @ X4 @ X5 @ X6))
% 0.33/0.52          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.33/0.52      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.33/0.52  thf('3', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.33/0.52           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.33/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.33/0.52  thf('4', plain,
% 0.33/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf(redefinition_k9_subset_1, axiom,
% 0.33/0.52    (![A:$i,B:$i,C:$i]:
% 0.33/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.33/0.52       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.33/0.52  thf('5', plain,
% 0.33/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.33/0.52         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.33/0.52          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.33/0.52      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.33/0.52  thf('6', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.33/0.52           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.33/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.33/0.52  thf('7', plain,
% 0.33/0.52      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 0.33/0.52         = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.33/0.52      inference('sup+', [status(thm)], ['3', '6'])).
% 0.33/0.52  thf(commutativity_k3_xboole_0, axiom,
% 0.33/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.33/0.52  thf('8', plain,
% 0.33/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.33/0.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.33/0.52  thf('9', plain,
% 0.33/0.52      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 0.33/0.52         = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.33/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.33/0.52  thf('10', plain, (~ (v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.33/0.52      inference('demod', [status(thm)], ['0', '9'])).
% 0.33/0.52  thf('11', plain,
% 0.33/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('12', plain,
% 0.33/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf(t35_tops_1, axiom,
% 0.33/0.52    (![A:$i]:
% 0.33/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.33/0.52       ( ![B:$i]:
% 0.33/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.33/0.52           ( ![C:$i]:
% 0.33/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.33/0.52               ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 0.33/0.52                 ( v4_pre_topc @
% 0.33/0.52                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.33/0.52  thf('13', plain,
% 0.33/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.33/0.52         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.33/0.52          | ~ (v4_pre_topc @ X13 @ X14)
% 0.33/0.52          | ~ (v4_pre_topc @ X15 @ X14)
% 0.33/0.52          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ X14) @ X13 @ X15) @ 
% 0.33/0.52             X14)
% 0.33/0.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.33/0.52          | ~ (l1_pre_topc @ X14)
% 0.33/0.52          | ~ (v2_pre_topc @ X14))),
% 0.33/0.52      inference('cnf', [status(esa)], [t35_tops_1])).
% 0.33/0.52  thf('14', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         (~ (v2_pre_topc @ sk_A)
% 0.33/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.33/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.33/0.52          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.33/0.52             sk_A)
% 0.33/0.52          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.33/0.52          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.33/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.33/0.52  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('17', plain,
% 0.33/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('18', plain,
% 0.33/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.33/0.52         (((k9_subset_1 @ X4 @ X6 @ X5) = (k9_subset_1 @ X4 @ X5 @ X6))
% 0.33/0.52          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.33/0.52      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.33/0.52  thf('19', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.33/0.52           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.33/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.33/0.52  thf('20', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.33/0.52           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.33/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.33/0.52  thf('21', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         ((k3_xboole_0 @ X0 @ sk_B)
% 0.33/0.52           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.33/0.52      inference('demod', [status(thm)], ['19', '20'])).
% 0.33/0.52  thf('22', plain,
% 0.33/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf(t16_compts_1, axiom,
% 0.33/0.52    (![A:$i]:
% 0.33/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.33/0.52       ( ![B:$i]:
% 0.33/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.33/0.52           ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) ) =>
% 0.33/0.52             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.33/0.52  thf('23', plain,
% 0.33/0.52      (![X16 : $i, X17 : $i]:
% 0.33/0.52         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.33/0.52          | (v4_pre_topc @ X16 @ X17)
% 0.33/0.52          | ~ (v2_compts_1 @ X16 @ X17)
% 0.33/0.52          | ~ (v8_pre_topc @ X17)
% 0.33/0.52          | ~ (l1_pre_topc @ X17)
% 0.33/0.52          | ~ (v2_pre_topc @ X17))),
% 0.33/0.52      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.33/0.52  thf('24', plain,
% 0.33/0.52      ((~ (v2_pre_topc @ sk_A)
% 0.33/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.33/0.52        | ~ (v8_pre_topc @ sk_A)
% 0.33/0.52        | ~ (v2_compts_1 @ sk_B @ sk_A)
% 0.33/0.52        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.33/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.33/0.52  thf('25', plain, ((v2_pre_topc @ sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('27', plain, ((v8_pre_topc @ sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('28', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('29', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.33/0.52      inference('demod', [status(thm)], ['24', '25', '26', '27', '28'])).
% 0.33/0.52  thf('30', plain,
% 0.33/0.52      (![X0 : $i]:
% 0.33/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.33/0.52          | (v4_pre_topc @ (k3_xboole_0 @ X0 @ sk_B) @ sk_A)
% 0.33/0.52          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.33/0.52      inference('demod', [status(thm)], ['14', '15', '16', '21', '29'])).
% 0.33/0.52  thf('31', plain,
% 0.33/0.52      ((~ (v4_pre_topc @ sk_C @ sk_A)
% 0.33/0.52        | (v4_pre_topc @ (k3_xboole_0 @ sk_C @ sk_B) @ sk_A))),
% 0.33/0.52      inference('sup-', [status(thm)], ['11', '30'])).
% 0.33/0.52  thf('32', plain,
% 0.33/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('33', plain,
% 0.33/0.52      (![X16 : $i, X17 : $i]:
% 0.33/0.52         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.33/0.52          | (v4_pre_topc @ X16 @ X17)
% 0.33/0.52          | ~ (v2_compts_1 @ X16 @ X17)
% 0.33/0.52          | ~ (v8_pre_topc @ X17)
% 0.33/0.52          | ~ (l1_pre_topc @ X17)
% 0.33/0.52          | ~ (v2_pre_topc @ X17))),
% 0.33/0.52      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.33/0.52  thf('34', plain,
% 0.33/0.52      ((~ (v2_pre_topc @ sk_A)
% 0.33/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.33/0.52        | ~ (v8_pre_topc @ sk_A)
% 0.33/0.52        | ~ (v2_compts_1 @ sk_C @ sk_A)
% 0.33/0.52        | (v4_pre_topc @ sk_C @ sk_A))),
% 0.33/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.33/0.52  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('37', plain, ((v8_pre_topc @ sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.52  thf('38', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.33/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('39', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.33/0.53      inference('demod', [status(thm)], ['34', '35', '36', '37', '38'])).
% 0.33/0.53  thf('40', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.33/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.33/0.53  thf('41', plain, ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.33/0.53      inference('demod', [status(thm)], ['31', '39', '40'])).
% 0.33/0.53  thf('42', plain,
% 0.33/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf(dt_k9_subset_1, axiom,
% 0.33/0.53    (![A:$i,B:$i,C:$i]:
% 0.33/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.33/0.53       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.33/0.53  thf('43', plain,
% 0.33/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.33/0.53         ((m1_subset_1 @ (k9_subset_1 @ X7 @ X8 @ X9) @ (k1_zfmisc_1 @ X7))
% 0.33/0.53          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X7)))),
% 0.33/0.53      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.33/0.53  thf('44', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ 
% 0.33/0.53          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.33/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.33/0.53  thf('45', plain,
% 0.33/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('46', plain,
% 0.33/0.53      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.33/0.53         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.33/0.53          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.33/0.53      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.33/0.53  thf('47', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.33/0.53           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.33/0.53      inference('sup-', [status(thm)], ['45', '46'])).
% 0.33/0.53  thf('48', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 0.33/0.53          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.33/0.53      inference('demod', [status(thm)], ['44', '47'])).
% 0.33/0.53  thf('49', plain,
% 0.33/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf(t18_compts_1, axiom,
% 0.33/0.53    (![A:$i]:
% 0.33/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.33/0.53       ( ![B:$i]:
% 0.33/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.33/0.53           ( ![C:$i]:
% 0.33/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.33/0.53               ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 0.33/0.53                   ( v4_pre_topc @ C @ A ) ) =>
% 0.33/0.53                 ( v2_compts_1 @ C @ A ) ) ) ) ) ) ))).
% 0.33/0.53  thf('50', plain,
% 0.33/0.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.33/0.53         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.33/0.53          | ~ (v2_compts_1 @ X18 @ X19)
% 0.33/0.53          | ~ (r1_tarski @ X20 @ X18)
% 0.33/0.53          | ~ (v4_pre_topc @ X20 @ X19)
% 0.33/0.53          | (v2_compts_1 @ X20 @ X19)
% 0.33/0.53          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.33/0.53          | ~ (l1_pre_topc @ X19)
% 0.33/0.53          | ~ (v2_pre_topc @ X19))),
% 0.33/0.53      inference('cnf', [status(esa)], [t18_compts_1])).
% 0.33/0.53  thf('51', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         (~ (v2_pre_topc @ sk_A)
% 0.33/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.33/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.33/0.53          | (v2_compts_1 @ X0 @ sk_A)
% 0.33/0.53          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.33/0.53          | ~ (r1_tarski @ X0 @ sk_C)
% 0.33/0.53          | ~ (v2_compts_1 @ sk_C @ sk_A))),
% 0.33/0.53      inference('sup-', [status(thm)], ['49', '50'])).
% 0.33/0.53  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('54', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.33/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.53  thf('55', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.33/0.53          | (v2_compts_1 @ X0 @ sk_A)
% 0.33/0.53          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.33/0.53          | ~ (r1_tarski @ X0 @ sk_C))),
% 0.33/0.53      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.33/0.53  thf('56', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ sk_C)
% 0.33/0.53          | ~ (v4_pre_topc @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A)
% 0.33/0.53          | (v2_compts_1 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A))),
% 0.33/0.53      inference('sup-', [status(thm)], ['48', '55'])).
% 0.33/0.53  thf('57', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.33/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.33/0.53  thf(t17_xboole_1, axiom,
% 0.33/0.53    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.33/0.53  thf('58', plain,
% 0.33/0.53      (![X2 : $i, X3 : $i]: (r1_tarski @ (k3_xboole_0 @ X2 @ X3) @ X2)),
% 0.33/0.53      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.33/0.53  thf('59', plain,
% 0.33/0.53      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.33/0.53      inference('sup+', [status(thm)], ['57', '58'])).
% 0.33/0.53  thf('60', plain,
% 0.33/0.53      (![X0 : $i]:
% 0.33/0.53         (~ (v4_pre_topc @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A)
% 0.33/0.53          | (v2_compts_1 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A))),
% 0.33/0.53      inference('demod', [status(thm)], ['56', '59'])).
% 0.33/0.53  thf('61', plain, ((v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.33/0.53      inference('sup-', [status(thm)], ['41', '60'])).
% 0.33/0.53  thf('62', plain, ($false), inference('demod', [status(thm)], ['10', '61'])).
% 0.33/0.53  
% 0.33/0.53  % SZS output end Refutation
% 0.33/0.53  
% 0.33/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
