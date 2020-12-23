%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ArkWjX8DYj

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:35 EST 2020

% Result     : Theorem 0.64s
% Output     : Refutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 171 expanded)
%              Number of leaves         :   28 (  64 expanded)
%              Depth                    :   10
%              Number of atoms          :  758 (2245 expanded)
%              Number of equality atoms :   22 (  45 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X9 @ X11 @ X10 )
        = ( k9_subset_1 @ X9 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X14 @ X12 @ X13 )
        = ( k3_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v4_pre_topc @ X23 @ X24 )
      | ~ ( v2_compts_1 @ X23 @ X24 )
      | ~ ( v8_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('21',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['21','22','23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','18','26'])).

thf('28',plain,
    ( ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ( v4_pre_topc @ ( k3_xboole_0 @ sk_C @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v4_pre_topc @ X23 @ X24 )
      | ~ ( v2_compts_1 @ X23 @ X24 )
      | ~ ( v8_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('31',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_C @ sk_A )
    | ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v4_pre_topc @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('37',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_tarski @ X8 @ X7 )
      = ( k2_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['28','36','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('46',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('47',plain,
    ( ( k3_xboole_0 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    = sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('50',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['47','56'])).

thf('58',plain,(
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

thf('59',plain,(
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

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_compts_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_C )
      | ~ ( v4_pre_topc @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('67',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A )
      | ( v2_compts_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','68'])).

thf('70',plain,(
    v2_compts_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['42','69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['4','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ArkWjX8DYj
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:23:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.64/0.86  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.64/0.86  % Solved by: fo/fo7.sh
% 0.64/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.64/0.86  % done 779 iterations in 0.409s
% 0.64/0.86  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.64/0.86  % SZS output start Refutation
% 0.64/0.86  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.64/0.86  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.64/0.86  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.64/0.86  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.64/0.86  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.64/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.64/0.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.64/0.86  thf(sk_C_type, type, sk_C: $i).
% 0.64/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.64/0.86  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.64/0.86  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.64/0.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.64/0.86  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.64/0.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.64/0.86  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.64/0.86  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.64/0.86  thf(t20_compts_1, conjecture,
% 0.64/0.86    (![A:$i]:
% 0.64/0.86     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.64/0.86       ( ![B:$i]:
% 0.64/0.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.64/0.86           ( ![C:$i]:
% 0.64/0.86             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.64/0.86               ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.64/0.86                   ( v2_compts_1 @ C @ A ) ) =>
% 0.64/0.86                 ( v2_compts_1 @
% 0.64/0.86                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.64/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.64/0.86    (~( ![A:$i]:
% 0.64/0.86        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.64/0.86          ( ![B:$i]:
% 0.64/0.86            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.64/0.86              ( ![C:$i]:
% 0.64/0.86                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.64/0.86                  ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.64/0.86                      ( v2_compts_1 @ C @ A ) ) =>
% 0.64/0.86                    ( v2_compts_1 @
% 0.64/0.86                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.64/0.86    inference('cnf.neg', [status(esa)], [t20_compts_1])).
% 0.64/0.86  thf('0', plain,
% 0.64/0.86      (~ (v2_compts_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.64/0.86          sk_A)),
% 0.64/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.86  thf('1', plain,
% 0.64/0.86      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.64/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.86  thf(redefinition_k9_subset_1, axiom,
% 0.64/0.86    (![A:$i,B:$i,C:$i]:
% 0.64/0.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.64/0.86       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.64/0.86  thf('2', plain,
% 0.64/0.86      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.64/0.86         (((k9_subset_1 @ X14 @ X12 @ X13) = (k3_xboole_0 @ X12 @ X13))
% 0.64/0.86          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.64/0.86      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.64/0.86  thf('3', plain,
% 0.64/0.86      (![X0 : $i]:
% 0.64/0.86         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.64/0.86           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.64/0.86      inference('sup-', [status(thm)], ['1', '2'])).
% 0.64/0.86  thf('4', plain, (~ (v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.64/0.86      inference('demod', [status(thm)], ['0', '3'])).
% 0.64/0.86  thf('5', plain,
% 0.64/0.86      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.64/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.86  thf('6', plain,
% 0.64/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.64/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.86  thf(t35_tops_1, axiom,
% 0.64/0.86    (![A:$i]:
% 0.64/0.86     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.64/0.86       ( ![B:$i]:
% 0.64/0.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.64/0.86           ( ![C:$i]:
% 0.64/0.86             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.64/0.86               ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 0.64/0.86                 ( v4_pre_topc @
% 0.64/0.86                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.64/0.86  thf('7', plain,
% 0.64/0.86      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.64/0.86         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.64/0.86          | ~ (v4_pre_topc @ X20 @ X21)
% 0.64/0.86          | ~ (v4_pre_topc @ X22 @ X21)
% 0.64/0.86          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ X21) @ X20 @ X22) @ 
% 0.64/0.86             X21)
% 0.64/0.86          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.64/0.86          | ~ (l1_pre_topc @ X21)
% 0.64/0.86          | ~ (v2_pre_topc @ X21))),
% 0.64/0.86      inference('cnf', [status(esa)], [t35_tops_1])).
% 0.64/0.86  thf('8', plain,
% 0.64/0.86      (![X0 : $i]:
% 0.64/0.86         (~ (v2_pre_topc @ sk_A)
% 0.64/0.86          | ~ (l1_pre_topc @ sk_A)
% 0.64/0.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.64/0.86          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.64/0.86             sk_A)
% 0.64/0.86          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.64/0.86          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.64/0.86      inference('sup-', [status(thm)], ['6', '7'])).
% 0.64/0.86  thf('9', plain, ((v2_pre_topc @ sk_A)),
% 0.64/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.86  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.64/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.86  thf('11', plain,
% 0.64/0.86      (![X0 : $i]:
% 0.64/0.86         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.64/0.86          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.64/0.86             sk_A)
% 0.64/0.86          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.64/0.86          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.64/0.86      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.64/0.86  thf('12', plain,
% 0.64/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.64/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.86  thf(commutativity_k9_subset_1, axiom,
% 0.64/0.86    (![A:$i,B:$i,C:$i]:
% 0.64/0.86     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.64/0.86       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.64/0.86  thf('13', plain,
% 0.64/0.86      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.64/0.86         (((k9_subset_1 @ X9 @ X11 @ X10) = (k9_subset_1 @ X9 @ X10 @ X11))
% 0.64/0.86          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.64/0.86      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.64/0.86  thf('14', plain,
% 0.64/0.86      (![X0 : $i]:
% 0.64/0.86         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.64/0.86           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.64/0.86      inference('sup-', [status(thm)], ['12', '13'])).
% 0.64/0.86  thf('15', plain,
% 0.64/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.64/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.86  thf('16', plain,
% 0.64/0.86      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.64/0.86         (((k9_subset_1 @ X14 @ X12 @ X13) = (k3_xboole_0 @ X12 @ X13))
% 0.64/0.86          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.64/0.86      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.64/0.86  thf('17', plain,
% 0.64/0.86      (![X0 : $i]:
% 0.64/0.86         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.64/0.86           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.64/0.86      inference('sup-', [status(thm)], ['15', '16'])).
% 0.64/0.86  thf('18', plain,
% 0.64/0.86      (![X0 : $i]:
% 0.64/0.86         ((k3_xboole_0 @ X0 @ sk_B)
% 0.64/0.86           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.64/0.86      inference('demod', [status(thm)], ['14', '17'])).
% 0.64/0.86  thf('19', plain,
% 0.64/0.86      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.64/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.86  thf(t16_compts_1, axiom,
% 0.64/0.86    (![A:$i]:
% 0.64/0.86     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.64/0.86       ( ![B:$i]:
% 0.64/0.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.64/0.86           ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) ) =>
% 0.64/0.86             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.64/0.86  thf('20', plain,
% 0.64/0.86      (![X23 : $i, X24 : $i]:
% 0.64/0.86         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.64/0.86          | (v4_pre_topc @ X23 @ X24)
% 0.64/0.86          | ~ (v2_compts_1 @ X23 @ X24)
% 0.64/0.86          | ~ (v8_pre_topc @ X24)
% 0.64/0.86          | ~ (l1_pre_topc @ X24)
% 0.64/0.86          | ~ (v2_pre_topc @ X24))),
% 0.64/0.86      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.64/0.86  thf('21', plain,
% 0.64/0.86      ((~ (v2_pre_topc @ sk_A)
% 0.64/0.86        | ~ (l1_pre_topc @ sk_A)
% 0.64/0.86        | ~ (v8_pre_topc @ sk_A)
% 0.64/0.86        | ~ (v2_compts_1 @ sk_B @ sk_A)
% 0.64/0.86        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.64/0.86      inference('sup-', [status(thm)], ['19', '20'])).
% 0.64/0.86  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.64/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.86  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.64/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.86  thf('24', plain, ((v8_pre_topc @ sk_A)),
% 0.64/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.86  thf('25', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.64/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.86  thf('26', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.64/0.86      inference('demod', [status(thm)], ['21', '22', '23', '24', '25'])).
% 0.64/0.86  thf('27', plain,
% 0.64/0.86      (![X0 : $i]:
% 0.64/0.86         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.64/0.86          | (v4_pre_topc @ (k3_xboole_0 @ X0 @ sk_B) @ sk_A)
% 0.64/0.86          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.64/0.86      inference('demod', [status(thm)], ['11', '18', '26'])).
% 0.64/0.86  thf('28', plain,
% 0.64/0.86      ((~ (v4_pre_topc @ sk_C @ sk_A)
% 0.64/0.86        | (v4_pre_topc @ (k3_xboole_0 @ sk_C @ sk_B) @ sk_A))),
% 0.64/0.86      inference('sup-', [status(thm)], ['5', '27'])).
% 0.64/0.86  thf('29', plain,
% 0.64/0.86      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.64/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.86  thf('30', plain,
% 0.64/0.86      (![X23 : $i, X24 : $i]:
% 0.64/0.86         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.64/0.86          | (v4_pre_topc @ X23 @ X24)
% 0.64/0.86          | ~ (v2_compts_1 @ X23 @ X24)
% 0.64/0.86          | ~ (v8_pre_topc @ X24)
% 0.64/0.86          | ~ (l1_pre_topc @ X24)
% 0.64/0.86          | ~ (v2_pre_topc @ X24))),
% 0.64/0.86      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.64/0.86  thf('31', plain,
% 0.64/0.86      ((~ (v2_pre_topc @ sk_A)
% 0.64/0.86        | ~ (l1_pre_topc @ sk_A)
% 0.64/0.86        | ~ (v8_pre_topc @ sk_A)
% 0.64/0.86        | ~ (v2_compts_1 @ sk_C @ sk_A)
% 0.64/0.86        | (v4_pre_topc @ sk_C @ sk_A))),
% 0.64/0.86      inference('sup-', [status(thm)], ['29', '30'])).
% 0.64/0.86  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.64/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.86  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.64/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.86  thf('34', plain, ((v8_pre_topc @ sk_A)),
% 0.64/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.86  thf('35', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.64/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.86  thf('36', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.64/0.86      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 0.64/0.86  thf(commutativity_k2_tarski, axiom,
% 0.64/0.86    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.64/0.86  thf('37', plain,
% 0.64/0.86      (![X7 : $i, X8 : $i]: ((k2_tarski @ X8 @ X7) = (k2_tarski @ X7 @ X8))),
% 0.64/0.86      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.64/0.86  thf(t12_setfam_1, axiom,
% 0.64/0.86    (![A:$i,B:$i]:
% 0.64/0.86     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.64/0.86  thf('38', plain,
% 0.64/0.86      (![X15 : $i, X16 : $i]:
% 0.64/0.86         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.64/0.86      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.64/0.86  thf('39', plain,
% 0.64/0.86      (![X0 : $i, X1 : $i]:
% 0.64/0.86         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.64/0.86      inference('sup+', [status(thm)], ['37', '38'])).
% 0.64/0.86  thf('40', plain,
% 0.64/0.86      (![X15 : $i, X16 : $i]:
% 0.64/0.86         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.64/0.86      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.64/0.86  thf('41', plain,
% 0.64/0.86      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.64/0.86      inference('sup+', [status(thm)], ['39', '40'])).
% 0.64/0.86  thf('42', plain, ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.64/0.86      inference('demod', [status(thm)], ['28', '36', '41'])).
% 0.64/0.86  thf('43', plain,
% 0.64/0.86      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.64/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.86  thf(t3_subset, axiom,
% 0.64/0.86    (![A:$i,B:$i]:
% 0.64/0.86     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.64/0.86  thf('44', plain,
% 0.64/0.86      (![X17 : $i, X18 : $i]:
% 0.64/0.86         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.64/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.64/0.86  thf('45', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.64/0.86      inference('sup-', [status(thm)], ['43', '44'])).
% 0.64/0.86  thf(t28_xboole_1, axiom,
% 0.64/0.86    (![A:$i,B:$i]:
% 0.64/0.86     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.64/0.86  thf('46', plain,
% 0.64/0.86      (![X5 : $i, X6 : $i]:
% 0.64/0.86         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.64/0.86      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.64/0.86  thf('47', plain, (((k3_xboole_0 @ sk_C @ (u1_struct_0 @ sk_A)) = (sk_C))),
% 0.64/0.86      inference('sup-', [status(thm)], ['45', '46'])).
% 0.64/0.86  thf('48', plain,
% 0.64/0.86      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.64/0.86      inference('sup+', [status(thm)], ['39', '40'])).
% 0.64/0.86  thf('49', plain,
% 0.64/0.86      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.64/0.86      inference('sup+', [status(thm)], ['39', '40'])).
% 0.64/0.86  thf(t17_xboole_1, axiom,
% 0.64/0.86    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.64/0.86  thf('50', plain,
% 0.64/0.86      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.64/0.86      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.64/0.86  thf(t108_xboole_1, axiom,
% 0.64/0.86    (![A:$i,B:$i,C:$i]:
% 0.64/0.86     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 0.64/0.86  thf('51', plain,
% 0.64/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.86         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k3_xboole_0 @ X0 @ X2) @ X1))),
% 0.64/0.86      inference('cnf', [status(esa)], [t108_xboole_1])).
% 0.64/0.86  thf('52', plain,
% 0.64/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.86         (r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X2) @ X0)),
% 0.64/0.86      inference('sup-', [status(thm)], ['50', '51'])).
% 0.64/0.86  thf('53', plain,
% 0.64/0.86      (![X17 : $i, X19 : $i]:
% 0.64/0.86         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 0.64/0.86      inference('cnf', [status(esa)], [t3_subset])).
% 0.64/0.86  thf('54', plain,
% 0.64/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.86         (m1_subset_1 @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ X1) @ 
% 0.64/0.86          (k1_zfmisc_1 @ X0))),
% 0.64/0.86      inference('sup-', [status(thm)], ['52', '53'])).
% 0.64/0.86  thf('55', plain,
% 0.64/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.86         (m1_subset_1 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.64/0.86          (k1_zfmisc_1 @ X1))),
% 0.64/0.86      inference('sup+', [status(thm)], ['49', '54'])).
% 0.64/0.86  thf('56', plain,
% 0.64/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.86         (m1_subset_1 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.64/0.86          (k1_zfmisc_1 @ X0))),
% 0.64/0.86      inference('sup+', [status(thm)], ['48', '55'])).
% 0.64/0.86  thf('57', plain,
% 0.64/0.86      (![X0 : $i]:
% 0.64/0.86         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 0.64/0.86          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.64/0.86      inference('sup+', [status(thm)], ['47', '56'])).
% 0.64/0.86  thf('58', plain,
% 0.64/0.86      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.64/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.86  thf(t18_compts_1, axiom,
% 0.64/0.86    (![A:$i]:
% 0.64/0.86     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.64/0.86       ( ![B:$i]:
% 0.64/0.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.64/0.86           ( ![C:$i]:
% 0.64/0.86             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.64/0.86               ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 0.64/0.86                   ( v4_pre_topc @ C @ A ) ) =>
% 0.64/0.86                 ( v2_compts_1 @ C @ A ) ) ) ) ) ) ))).
% 0.64/0.86  thf('59', plain,
% 0.64/0.86      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.64/0.86         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.64/0.86          | ~ (v2_compts_1 @ X25 @ X26)
% 0.64/0.86          | ~ (r1_tarski @ X27 @ X25)
% 0.64/0.86          | ~ (v4_pre_topc @ X27 @ X26)
% 0.64/0.86          | (v2_compts_1 @ X27 @ X26)
% 0.64/0.86          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.64/0.86          | ~ (l1_pre_topc @ X26)
% 0.64/0.86          | ~ (v2_pre_topc @ X26))),
% 0.64/0.86      inference('cnf', [status(esa)], [t18_compts_1])).
% 0.64/0.86  thf('60', plain,
% 0.64/0.86      (![X0 : $i]:
% 0.64/0.86         (~ (v2_pre_topc @ sk_A)
% 0.64/0.86          | ~ (l1_pre_topc @ sk_A)
% 0.64/0.86          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.64/0.86          | (v2_compts_1 @ X0 @ sk_A)
% 0.64/0.86          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.64/0.86          | ~ (r1_tarski @ X0 @ sk_C)
% 0.64/0.86          | ~ (v2_compts_1 @ sk_C @ sk_A))),
% 0.64/0.86      inference('sup-', [status(thm)], ['58', '59'])).
% 0.64/0.86  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.64/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.86  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.64/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.86  thf('63', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.64/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.86  thf('64', plain,
% 0.64/0.86      (![X0 : $i]:
% 0.64/0.86         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.64/0.86          | (v2_compts_1 @ X0 @ sk_A)
% 0.64/0.86          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.64/0.86          | ~ (r1_tarski @ X0 @ sk_C))),
% 0.64/0.86      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 0.64/0.86  thf('65', plain,
% 0.64/0.86      (![X0 : $i]:
% 0.64/0.86         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ sk_C)
% 0.64/0.86          | ~ (v4_pre_topc @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A)
% 0.64/0.86          | (v2_compts_1 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A))),
% 0.64/0.86      inference('sup-', [status(thm)], ['57', '64'])).
% 0.64/0.86  thf('66', plain,
% 0.64/0.86      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.64/0.86      inference('sup+', [status(thm)], ['39', '40'])).
% 0.64/0.86  thf('67', plain,
% 0.64/0.86      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 0.64/0.86      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.64/0.86  thf('68', plain,
% 0.64/0.86      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.64/0.86      inference('sup+', [status(thm)], ['66', '67'])).
% 0.64/0.86  thf('69', plain,
% 0.64/0.86      (![X0 : $i]:
% 0.64/0.86         (~ (v4_pre_topc @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A)
% 0.64/0.86          | (v2_compts_1 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A))),
% 0.64/0.86      inference('demod', [status(thm)], ['65', '68'])).
% 0.64/0.86  thf('70', plain, ((v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.64/0.86      inference('sup-', [status(thm)], ['42', '69'])).
% 0.64/0.86  thf('71', plain, ($false), inference('demod', [status(thm)], ['4', '70'])).
% 0.64/0.86  
% 0.64/0.86  % SZS output end Refutation
% 0.64/0.86  
% 0.72/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
