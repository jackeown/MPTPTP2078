%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YOuZ8sJYcJ

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:35 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 208 expanded)
%              Number of leaves         :   33 (  77 expanded)
%              Depth                    :   10
%              Number of atoms          :  861 (3035 expanded)
%              Number of equality atoms :   26 (  52 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

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

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('8',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( ( k7_subset_1 @ X18 @ X19 @ X17 )
        = ( k9_subset_1 @ X18 @ X19 @ ( k3_subset_1 @ X18 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_subset_1 @ X10 @ ( k3_subset_1 @ X10 @ X9 ) )
        = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('13',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_subset_1 @ X16 @ X14 @ X15 )
        = ( k3_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
        = ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','13','16'])).

thf('18',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['5','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( ( k7_subset_1 @ X12 @ X11 @ X13 )
        = ( k4_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
      = ( k4_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X6 @ X5 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['18','21','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X22: $i,X24: $i] :
      ( ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
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

thf('36',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v2_compts_1 @ X30 @ X31 )
      | ~ ( r1_tarski @ X32 @ X30 )
      | ~ ( v4_pre_topc @ X32 @ X31 )
      | ( v2_compts_1 @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t18_compts_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_compts_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_C @ X0 ) @ sk_C )
      | ~ ( v4_pre_topc @ ( k4_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ( v2_compts_1 @ ( k4_xboole_0 @ sk_C @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('43',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k4_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ( v2_compts_1 @ ( k4_xboole_0 @ sk_C @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A )
    | ( v2_compts_1 @ ( k4_xboole_0 @ sk_C @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['27','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
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

thf('48',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v4_pre_topc @ X25 @ X26 )
      | ~ ( v4_pre_topc @ X27 @ X26 )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X26 ) @ X25 @ X27 ) @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t35_tops_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
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

thf('53',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v4_pre_topc @ X28 @ X29 )
      | ~ ( v2_compts_1 @ X28 @ X29 )
      | ~ ( v8_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('54',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50','51','59'])).

thf('61',plain,
    ( ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['46','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v4_pre_topc @ X28 @ X29 )
      | ~ ( v2_compts_1 @ X28 @ X29 )
      | ~ ( v8_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('64',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_C @ sk_A )
    | ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v4_pre_topc @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['64','65','66','67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('71',plain,(
    v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['61','69','70'])).

thf('72',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['18','21','26'])).

thf('73',plain,(
    v2_compts_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['45','71','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['4','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YOuZ8sJYcJ
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:02:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.51/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.76  % Solved by: fo/fo7.sh
% 0.51/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.76  % done 295 iterations in 0.302s
% 0.51/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.76  % SZS output start Refutation
% 0.51/0.76  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.51/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.76  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.76  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.51/0.76  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.51/0.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.51/0.76  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.51/0.76  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.51/0.76  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 0.51/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.76  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.51/0.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.51/0.76  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.51/0.76  thf(sk_C_type, type, sk_C: $i).
% 0.51/0.76  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.51/0.76  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.51/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.76  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.51/0.76  thf(t20_compts_1, conjecture,
% 0.51/0.76    (![A:$i]:
% 0.51/0.76     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.76       ( ![B:$i]:
% 0.51/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.76           ( ![C:$i]:
% 0.51/0.76             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.76               ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.51/0.76                   ( v2_compts_1 @ C @ A ) ) =>
% 0.51/0.76                 ( v2_compts_1 @
% 0.51/0.76                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.51/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.76    (~( ![A:$i]:
% 0.51/0.76        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.76          ( ![B:$i]:
% 0.51/0.76            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.76              ( ![C:$i]:
% 0.51/0.76                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.76                  ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 0.51/0.76                      ( v2_compts_1 @ C @ A ) ) =>
% 0.51/0.76                    ( v2_compts_1 @
% 0.51/0.76                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.51/0.76    inference('cnf.neg', [status(esa)], [t20_compts_1])).
% 0.51/0.76  thf('0', plain,
% 0.51/0.76      (~ (v2_compts_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.51/0.76          sk_A)),
% 0.51/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.76  thf('1', plain,
% 0.51/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.76  thf(redefinition_k9_subset_1, axiom,
% 0.51/0.76    (![A:$i,B:$i,C:$i]:
% 0.51/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.76       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.51/0.76  thf('2', plain,
% 0.51/0.76      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.51/0.76         (((k9_subset_1 @ X16 @ X14 @ X15) = (k3_xboole_0 @ X14 @ X15))
% 0.51/0.76          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.51/0.76      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.51/0.76  thf('3', plain,
% 0.51/0.76      (![X0 : $i]:
% 0.51/0.76         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.51/0.76           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.51/0.76      inference('sup-', [status(thm)], ['1', '2'])).
% 0.51/0.76  thf('4', plain, (~ (v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.51/0.76      inference('demod', [status(thm)], ['0', '3'])).
% 0.51/0.76  thf('5', plain,
% 0.51/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.76  thf('6', plain,
% 0.51/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.76  thf(dt_k3_subset_1, axiom,
% 0.51/0.76    (![A:$i,B:$i]:
% 0.51/0.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.76       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.51/0.76  thf('7', plain,
% 0.51/0.76      (![X7 : $i, X8 : $i]:
% 0.51/0.76         ((m1_subset_1 @ (k3_subset_1 @ X7 @ X8) @ (k1_zfmisc_1 @ X7))
% 0.51/0.76          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.51/0.76      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.51/0.76  thf('8', plain,
% 0.51/0.76      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.51/0.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.76      inference('sup-', [status(thm)], ['6', '7'])).
% 0.51/0.76  thf(t32_subset_1, axiom,
% 0.51/0.76    (![A:$i,B:$i]:
% 0.51/0.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.76       ( ![C:$i]:
% 0.51/0.76         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.76           ( ( k7_subset_1 @ A @ B @ C ) =
% 0.51/0.76             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.51/0.76  thf('9', plain,
% 0.51/0.76      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.51/0.76         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.51/0.76          | ((k7_subset_1 @ X18 @ X19 @ X17)
% 0.51/0.76              = (k9_subset_1 @ X18 @ X19 @ (k3_subset_1 @ X18 @ X17)))
% 0.51/0.76          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.51/0.76      inference('cnf', [status(esa)], [t32_subset_1])).
% 0.51/0.76  thf('10', plain,
% 0.51/0.76      (![X0 : $i]:
% 0.51/0.76         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.76          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.51/0.76              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.51/0.76              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.51/0.76                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.51/0.76                  (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.51/0.76      inference('sup-', [status(thm)], ['8', '9'])).
% 0.51/0.76  thf('11', plain,
% 0.51/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.76  thf(involutiveness_k3_subset_1, axiom,
% 0.51/0.76    (![A:$i,B:$i]:
% 0.51/0.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.76       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.51/0.76  thf('12', plain,
% 0.51/0.76      (![X9 : $i, X10 : $i]:
% 0.51/0.76         (((k3_subset_1 @ X10 @ (k3_subset_1 @ X10 @ X9)) = (X9))
% 0.51/0.76          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.51/0.76      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.51/0.76  thf('13', plain,
% 0.51/0.76      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.51/0.76         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.51/0.76      inference('sup-', [status(thm)], ['11', '12'])).
% 0.51/0.76  thf('14', plain,
% 0.51/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.76  thf('15', plain,
% 0.51/0.76      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.51/0.76         (((k9_subset_1 @ X16 @ X14 @ X15) = (k3_xboole_0 @ X14 @ X15))
% 0.51/0.76          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.51/0.76      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.51/0.76  thf('16', plain,
% 0.51/0.76      (![X0 : $i]:
% 0.51/0.76         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.51/0.76           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.51/0.76      inference('sup-', [status(thm)], ['14', '15'])).
% 0.51/0.76  thf('17', plain,
% 0.51/0.76      (![X0 : $i]:
% 0.51/0.76         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.76          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.51/0.76              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.51/0.76              = (k3_xboole_0 @ X0 @ sk_B)))),
% 0.51/0.76      inference('demod', [status(thm)], ['10', '13', '16'])).
% 0.51/0.76  thf('18', plain,
% 0.51/0.76      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.51/0.76         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.51/0.76         = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.51/0.76      inference('sup-', [status(thm)], ['5', '17'])).
% 0.51/0.76  thf('19', plain,
% 0.51/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.76  thf(redefinition_k7_subset_1, axiom,
% 0.51/0.76    (![A:$i,B:$i,C:$i]:
% 0.51/0.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.76       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.51/0.76  thf('20', plain,
% 0.51/0.76      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.51/0.76         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.51/0.76          | ((k7_subset_1 @ X12 @ X11 @ X13) = (k4_xboole_0 @ X11 @ X13)))),
% 0.51/0.76      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.51/0.76  thf('21', plain,
% 0.51/0.76      (![X0 : $i]:
% 0.51/0.76         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)
% 0.51/0.76           = (k4_xboole_0 @ sk_C @ X0))),
% 0.51/0.76      inference('sup-', [status(thm)], ['19', '20'])).
% 0.51/0.76  thf(commutativity_k2_tarski, axiom,
% 0.51/0.76    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.51/0.76  thf('22', plain,
% 0.51/0.76      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 0.51/0.76      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.51/0.76  thf(t12_setfam_1, axiom,
% 0.51/0.76    (![A:$i,B:$i]:
% 0.51/0.76     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.51/0.76  thf('23', plain,
% 0.51/0.76      (![X20 : $i, X21 : $i]:
% 0.51/0.76         ((k1_setfam_1 @ (k2_tarski @ X20 @ X21)) = (k3_xboole_0 @ X20 @ X21))),
% 0.51/0.76      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.51/0.76  thf('24', plain,
% 0.51/0.76      (![X0 : $i, X1 : $i]:
% 0.51/0.76         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.76      inference('sup+', [status(thm)], ['22', '23'])).
% 0.51/0.76  thf('25', plain,
% 0.51/0.76      (![X20 : $i, X21 : $i]:
% 0.51/0.76         ((k1_setfam_1 @ (k2_tarski @ X20 @ X21)) = (k3_xboole_0 @ X20 @ X21))),
% 0.51/0.76      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.51/0.76  thf('26', plain,
% 0.51/0.76      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.76      inference('sup+', [status(thm)], ['24', '25'])).
% 0.51/0.76  thf('27', plain,
% 0.51/0.76      (((k4_xboole_0 @ sk_C @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.51/0.76         = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.51/0.76      inference('demod', [status(thm)], ['18', '21', '26'])).
% 0.51/0.76  thf('28', plain,
% 0.51/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.76  thf(t3_subset, axiom,
% 0.51/0.76    (![A:$i,B:$i]:
% 0.51/0.76     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.51/0.76  thf('29', plain,
% 0.51/0.76      (![X22 : $i, X23 : $i]:
% 0.51/0.76         ((r1_tarski @ X22 @ X23) | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 0.51/0.76      inference('cnf', [status(esa)], [t3_subset])).
% 0.51/0.76  thf('30', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.51/0.76      inference('sup-', [status(thm)], ['28', '29'])).
% 0.51/0.76  thf(t109_xboole_1, axiom,
% 0.51/0.76    (![A:$i,B:$i,C:$i]:
% 0.51/0.76     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.51/0.76  thf('31', plain,
% 0.51/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.76         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k4_xboole_0 @ X0 @ X2) @ X1))),
% 0.51/0.76      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.51/0.76  thf('32', plain,
% 0.51/0.76      (![X0 : $i]:
% 0.51/0.76         (r1_tarski @ (k4_xboole_0 @ sk_C @ X0) @ (u1_struct_0 @ sk_A))),
% 0.51/0.76      inference('sup-', [status(thm)], ['30', '31'])).
% 0.51/0.76  thf('33', plain,
% 0.51/0.76      (![X22 : $i, X24 : $i]:
% 0.51/0.76         ((m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X22 @ X24))),
% 0.51/0.76      inference('cnf', [status(esa)], [t3_subset])).
% 0.51/0.76  thf('34', plain,
% 0.51/0.76      (![X0 : $i]:
% 0.51/0.76         (m1_subset_1 @ (k4_xboole_0 @ sk_C @ X0) @ 
% 0.51/0.76          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.76      inference('sup-', [status(thm)], ['32', '33'])).
% 0.51/0.76  thf('35', plain,
% 0.51/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.76  thf(t18_compts_1, axiom,
% 0.51/0.76    (![A:$i]:
% 0.51/0.76     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.76       ( ![B:$i]:
% 0.51/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.76           ( ![C:$i]:
% 0.51/0.76             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.76               ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 0.51/0.76                   ( v4_pre_topc @ C @ A ) ) =>
% 0.51/0.76                 ( v2_compts_1 @ C @ A ) ) ) ) ) ) ))).
% 0.51/0.76  thf('36', plain,
% 0.51/0.76      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.51/0.76         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.51/0.76          | ~ (v2_compts_1 @ X30 @ X31)
% 0.51/0.76          | ~ (r1_tarski @ X32 @ X30)
% 0.51/0.76          | ~ (v4_pre_topc @ X32 @ X31)
% 0.51/0.76          | (v2_compts_1 @ X32 @ X31)
% 0.51/0.76          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.51/0.76          | ~ (l1_pre_topc @ X31)
% 0.51/0.76          | ~ (v2_pre_topc @ X31))),
% 0.51/0.76      inference('cnf', [status(esa)], [t18_compts_1])).
% 0.51/0.76  thf('37', plain,
% 0.51/0.76      (![X0 : $i]:
% 0.51/0.76         (~ (v2_pre_topc @ sk_A)
% 0.51/0.76          | ~ (l1_pre_topc @ sk_A)
% 0.51/0.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.76          | (v2_compts_1 @ X0 @ sk_A)
% 0.51/0.76          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.51/0.76          | ~ (r1_tarski @ X0 @ sk_C)
% 0.51/0.76          | ~ (v2_compts_1 @ sk_C @ sk_A))),
% 0.51/0.76      inference('sup-', [status(thm)], ['35', '36'])).
% 0.51/0.76  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.76  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.76  thf('40', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.51/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.76  thf('41', plain,
% 0.51/0.76      (![X0 : $i]:
% 0.51/0.76         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.76          | (v2_compts_1 @ X0 @ sk_A)
% 0.51/0.76          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.51/0.76          | ~ (r1_tarski @ X0 @ sk_C))),
% 0.51/0.76      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.51/0.76  thf('42', plain,
% 0.51/0.76      (![X0 : $i]:
% 0.51/0.76         (~ (r1_tarski @ (k4_xboole_0 @ sk_C @ X0) @ sk_C)
% 0.51/0.76          | ~ (v4_pre_topc @ (k4_xboole_0 @ sk_C @ X0) @ sk_A)
% 0.51/0.76          | (v2_compts_1 @ (k4_xboole_0 @ sk_C @ X0) @ sk_A))),
% 0.51/0.76      inference('sup-', [status(thm)], ['34', '41'])).
% 0.51/0.76  thf(t36_xboole_1, axiom,
% 0.51/0.76    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.51/0.76  thf('43', plain,
% 0.51/0.76      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 0.51/0.76      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.51/0.76  thf('44', plain,
% 0.51/0.76      (![X0 : $i]:
% 0.51/0.76         (~ (v4_pre_topc @ (k4_xboole_0 @ sk_C @ X0) @ sk_A)
% 0.51/0.76          | (v2_compts_1 @ (k4_xboole_0 @ sk_C @ X0) @ sk_A))),
% 0.51/0.76      inference('demod', [status(thm)], ['42', '43'])).
% 0.51/0.76  thf('45', plain,
% 0.51/0.76      ((~ (v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)
% 0.51/0.76        | (v2_compts_1 @ 
% 0.51/0.76           (k4_xboole_0 @ sk_C @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.51/0.76           sk_A))),
% 0.51/0.76      inference('sup-', [status(thm)], ['27', '44'])).
% 0.51/0.76  thf('46', plain,
% 0.51/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.76  thf('47', plain,
% 0.51/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.76  thf(t35_tops_1, axiom,
% 0.51/0.76    (![A:$i]:
% 0.51/0.76     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.76       ( ![B:$i]:
% 0.51/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.76           ( ![C:$i]:
% 0.51/0.76             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.76               ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 0.51/0.76                 ( v4_pre_topc @
% 0.51/0.76                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.51/0.76  thf('48', plain,
% 0.51/0.76      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.51/0.76         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.51/0.76          | ~ (v4_pre_topc @ X25 @ X26)
% 0.51/0.76          | ~ (v4_pre_topc @ X27 @ X26)
% 0.51/0.76          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ X26) @ X25 @ X27) @ 
% 0.51/0.76             X26)
% 0.51/0.76          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.51/0.76          | ~ (l1_pre_topc @ X26)
% 0.51/0.76          | ~ (v2_pre_topc @ X26))),
% 0.51/0.76      inference('cnf', [status(esa)], [t35_tops_1])).
% 0.51/0.76  thf('49', plain,
% 0.51/0.76      (![X0 : $i]:
% 0.51/0.76         (~ (v2_pre_topc @ sk_A)
% 0.51/0.76          | ~ (l1_pre_topc @ sk_A)
% 0.51/0.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.76          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.51/0.76             sk_A)
% 0.51/0.76          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.51/0.76          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.76      inference('sup-', [status(thm)], ['47', '48'])).
% 0.51/0.76  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.76  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.76  thf('52', plain,
% 0.51/0.76      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.76  thf(t16_compts_1, axiom,
% 0.51/0.76    (![A:$i]:
% 0.51/0.76     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.51/0.76       ( ![B:$i]:
% 0.51/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.76           ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) ) =>
% 0.51/0.76             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.51/0.76  thf('53', plain,
% 0.51/0.76      (![X28 : $i, X29 : $i]:
% 0.51/0.76         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.51/0.76          | (v4_pre_topc @ X28 @ X29)
% 0.51/0.76          | ~ (v2_compts_1 @ X28 @ X29)
% 0.51/0.76          | ~ (v8_pre_topc @ X29)
% 0.51/0.76          | ~ (l1_pre_topc @ X29)
% 0.51/0.76          | ~ (v2_pre_topc @ X29))),
% 0.51/0.76      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.51/0.76  thf('54', plain,
% 0.51/0.76      ((~ (v2_pre_topc @ sk_A)
% 0.51/0.76        | ~ (l1_pre_topc @ sk_A)
% 0.51/0.76        | ~ (v8_pre_topc @ sk_A)
% 0.51/0.76        | ~ (v2_compts_1 @ sk_B @ sk_A)
% 0.51/0.76        | (v4_pre_topc @ sk_B @ sk_A))),
% 0.51/0.76      inference('sup-', [status(thm)], ['52', '53'])).
% 0.51/0.76  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.76  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.76  thf('57', plain, ((v8_pre_topc @ sk_A)),
% 0.51/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.76  thf('58', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 0.51/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.76  thf('59', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.51/0.76      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 0.51/0.76  thf('60', plain,
% 0.51/0.76      (![X0 : $i]:
% 0.51/0.76         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.51/0.76          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.51/0.76             sk_A)
% 0.51/0.76          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.51/0.76      inference('demod', [status(thm)], ['49', '50', '51', '59'])).
% 0.51/0.76  thf('61', plain,
% 0.51/0.76      ((~ (v4_pre_topc @ sk_C @ sk_A)
% 0.51/0.76        | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.51/0.76           sk_A))),
% 0.51/0.76      inference('sup-', [status(thm)], ['46', '60'])).
% 0.51/0.76  thf('62', plain,
% 0.51/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.51/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.76  thf('63', plain,
% 0.51/0.76      (![X28 : $i, X29 : $i]:
% 0.51/0.76         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.51/0.76          | (v4_pre_topc @ X28 @ X29)
% 0.51/0.76          | ~ (v2_compts_1 @ X28 @ X29)
% 0.51/0.76          | ~ (v8_pre_topc @ X29)
% 0.51/0.76          | ~ (l1_pre_topc @ X29)
% 0.51/0.76          | ~ (v2_pre_topc @ X29))),
% 0.51/0.76      inference('cnf', [status(esa)], [t16_compts_1])).
% 0.51/0.76  thf('64', plain,
% 0.51/0.76      ((~ (v2_pre_topc @ sk_A)
% 0.51/0.76        | ~ (l1_pre_topc @ sk_A)
% 0.51/0.76        | ~ (v8_pre_topc @ sk_A)
% 0.51/0.76        | ~ (v2_compts_1 @ sk_C @ sk_A)
% 0.51/0.76        | (v4_pre_topc @ sk_C @ sk_A))),
% 0.51/0.76      inference('sup-', [status(thm)], ['62', '63'])).
% 0.51/0.76  thf('65', plain, ((v2_pre_topc @ sk_A)),
% 0.51/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.76  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.76  thf('67', plain, ((v8_pre_topc @ sk_A)),
% 0.51/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.76  thf('68', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 0.51/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.76  thf('69', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.51/0.76      inference('demod', [status(thm)], ['64', '65', '66', '67', '68'])).
% 0.51/0.76  thf('70', plain,
% 0.51/0.76      (![X0 : $i]:
% 0.51/0.76         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.51/0.76           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.51/0.76      inference('sup-', [status(thm)], ['1', '2'])).
% 0.51/0.76  thf('71', plain, ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.51/0.76      inference('demod', [status(thm)], ['61', '69', '70'])).
% 0.51/0.76  thf('72', plain,
% 0.51/0.76      (((k4_xboole_0 @ sk_C @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.51/0.76         = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.51/0.76      inference('demod', [status(thm)], ['18', '21', '26'])).
% 0.51/0.76  thf('73', plain, ((v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.51/0.76      inference('demod', [status(thm)], ['45', '71', '72'])).
% 0.51/0.76  thf('74', plain, ($false), inference('demod', [status(thm)], ['4', '73'])).
% 0.51/0.76  
% 0.51/0.76  % SZS output end Refutation
% 0.51/0.76  
% 0.51/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
