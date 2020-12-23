%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QcADHui7H9

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:35 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 226 expanded)
%              Number of leaves         :   38 (  84 expanded)
%              Depth                    :   11
%              Number of atoms          :  966 (3283 expanded)
%              Number of equality atoms :   29 (  53 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v8_pre_topc_type,type,(
    v8_pre_topc: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k9_subset_1 @ X13 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( ( k7_subset_1 @ X15 @ X16 @ X14 )
        = ( k9_subset_1 @ X15 @ X16 @ ( k3_subset_1 @ X15 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X7 @ ( k3_subset_1 @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('13',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k9_subset_1 @ X13 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( ( k7_subset_1 @ X9 @ X8 @ X10 )
        = ( k4_xboole_0 @ X8 @ X10 ) ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
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

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('29',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X22 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('30',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['30','31'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('34',plain,(
    ! [X19: $i,X21: $i] :
      ( ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ( m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('40',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X25 @ X24 ) )
        = X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['38','43','44'])).

thf('46',plain,(
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

thf('47',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( v2_compts_1 @ X34 @ X35 )
      | ~ ( r1_tarski @ X36 @ X34 )
      | ~ ( v4_pre_topc @ X36 @ X35 )
      | ( v2_compts_1 @ X36 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( v2_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t18_compts_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_compts_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_compts_1 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_C @ X0 ) @ sk_C )
      | ~ ( v4_pre_topc @ ( k4_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ( v2_compts_1 @ ( k4_xboole_0 @ sk_C @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ ( k4_xboole_0 @ sk_C @ X0 ) @ sk_A )
      | ( v2_compts_1 @ ( k4_xboole_0 @ sk_C @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A )
    | ( v2_compts_1 @ ( k4_xboole_0 @ sk_C @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['27','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
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

thf('59',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v4_pre_topc @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( v4_pre_topc @ X31 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v4_pre_topc @ ( k3_xboole_0 @ X29 @ X31 ) @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc4_tops_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
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

thf('64',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( v4_pre_topc @ X32 @ X33 )
      | ~ ( v2_compts_1 @ X32 @ X33 )
      | ~ ( v8_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('65',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_compts_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61','62','70'])).

thf('72',plain,
    ( ~ ( v4_pre_topc @ sk_C @ sk_A )
    | ( v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['57','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( v4_pre_topc @ X32 @ X33 )
      | ~ ( v2_compts_1 @ X32 @ X33 )
      | ~ ( v8_pre_topc @ X33 )
      | ~ ( l1_pre_topc @ X33 )
      | ~ ( v2_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t16_compts_1])).

thf('75',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v8_pre_topc @ sk_A )
    | ~ ( v2_compts_1 @ sk_C @ sk_A )
    | ( v4_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v8_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_compts_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v4_pre_topc @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['75','76','77','78','79'])).

thf('81',plain,(
    v4_pre_topc @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['72','80'])).

thf('82',plain,
    ( ( k4_xboole_0 @ sk_C @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['18','21','26'])).

thf('83',plain,(
    v2_compts_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['56','81','82'])).

thf('84',plain,(
    $false ),
    inference(demod,[status(thm)],['4','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QcADHui7H9
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:13:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.51/1.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.51/1.73  % Solved by: fo/fo7.sh
% 1.51/1.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.51/1.73  % done 769 iterations in 1.267s
% 1.51/1.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.51/1.73  % SZS output start Refutation
% 1.51/1.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.51/1.73  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.51/1.73  thf(sk_B_type, type, sk_B: $i).
% 1.51/1.73  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.51/1.73  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.51/1.73  thf(sk_A_type, type, sk_A: $i).
% 1.51/1.73  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.51/1.73  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.51/1.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.51/1.73  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.51/1.73  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.51/1.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.51/1.73  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 1.51/1.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.51/1.73  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 1.51/1.73  thf(sk_C_type, type, sk_C: $i).
% 1.51/1.73  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.51/1.73  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.51/1.73  thf(v8_pre_topc_type, type, v8_pre_topc: $i > $o).
% 1.51/1.73  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.51/1.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.51/1.73  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.51/1.73  thf(t20_compts_1, conjecture,
% 1.51/1.73    (![A:$i]:
% 1.51/1.73     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.51/1.73       ( ![B:$i]:
% 1.51/1.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.51/1.73           ( ![C:$i]:
% 1.51/1.73             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.51/1.73               ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 1.51/1.73                   ( v2_compts_1 @ C @ A ) ) =>
% 1.51/1.73                 ( v2_compts_1 @
% 1.51/1.73                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 1.51/1.73  thf(zf_stmt_0, negated_conjecture,
% 1.51/1.73    (~( ![A:$i]:
% 1.51/1.73        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.51/1.73          ( ![B:$i]:
% 1.51/1.73            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.51/1.73              ( ![C:$i]:
% 1.51/1.73                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.51/1.73                  ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) & 
% 1.51/1.73                      ( v2_compts_1 @ C @ A ) ) =>
% 1.51/1.73                    ( v2_compts_1 @
% 1.51/1.73                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 1.51/1.73    inference('cnf.neg', [status(esa)], [t20_compts_1])).
% 1.51/1.73  thf('0', plain,
% 1.51/1.73      (~ (v2_compts_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 1.51/1.73          sk_A)),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf('1', plain,
% 1.51/1.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf(redefinition_k9_subset_1, axiom,
% 1.51/1.73    (![A:$i,B:$i,C:$i]:
% 1.51/1.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.51/1.73       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.51/1.73  thf('2', plain,
% 1.51/1.73      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.51/1.73         (((k9_subset_1 @ X13 @ X11 @ X12) = (k3_xboole_0 @ X11 @ X12))
% 1.51/1.73          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 1.51/1.73      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.51/1.73  thf('3', plain,
% 1.51/1.73      (![X0 : $i]:
% 1.51/1.73         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 1.51/1.73           = (k3_xboole_0 @ X0 @ sk_C))),
% 1.51/1.73      inference('sup-', [status(thm)], ['1', '2'])).
% 1.51/1.73  thf('4', plain, (~ (v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 1.51/1.73      inference('demod', [status(thm)], ['0', '3'])).
% 1.51/1.73  thf('5', plain,
% 1.51/1.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf('6', plain,
% 1.51/1.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf(dt_k3_subset_1, axiom,
% 1.51/1.73    (![A:$i,B:$i]:
% 1.51/1.73     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.51/1.73       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.51/1.73  thf('7', plain,
% 1.51/1.73      (![X4 : $i, X5 : $i]:
% 1.51/1.73         ((m1_subset_1 @ (k3_subset_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4))
% 1.51/1.73          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 1.51/1.73      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.51/1.73  thf('8', plain,
% 1.51/1.73      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.51/1.73        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.73      inference('sup-', [status(thm)], ['6', '7'])).
% 1.51/1.73  thf(t32_subset_1, axiom,
% 1.51/1.73    (![A:$i,B:$i]:
% 1.51/1.73     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.51/1.73       ( ![C:$i]:
% 1.51/1.73         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.51/1.73           ( ( k7_subset_1 @ A @ B @ C ) =
% 1.51/1.73             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 1.51/1.73  thf('9', plain,
% 1.51/1.73      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.51/1.73         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 1.51/1.73          | ((k7_subset_1 @ X15 @ X16 @ X14)
% 1.51/1.73              = (k9_subset_1 @ X15 @ X16 @ (k3_subset_1 @ X15 @ X14)))
% 1.51/1.73          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 1.51/1.73      inference('cnf', [status(esa)], [t32_subset_1])).
% 1.51/1.73  thf('10', plain,
% 1.51/1.73      (![X0 : $i]:
% 1.51/1.73         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.51/1.73          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.51/1.73              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.51/1.73              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.51/1.73                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.51/1.73                  (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.51/1.73      inference('sup-', [status(thm)], ['8', '9'])).
% 1.51/1.73  thf('11', plain,
% 1.51/1.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf(involutiveness_k3_subset_1, axiom,
% 1.51/1.73    (![A:$i,B:$i]:
% 1.51/1.73     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.51/1.73       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.51/1.73  thf('12', plain,
% 1.51/1.73      (![X6 : $i, X7 : $i]:
% 1.51/1.73         (((k3_subset_1 @ X7 @ (k3_subset_1 @ X7 @ X6)) = (X6))
% 1.51/1.73          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 1.51/1.73      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.51/1.73  thf('13', plain,
% 1.51/1.73      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.51/1.73         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.51/1.73      inference('sup-', [status(thm)], ['11', '12'])).
% 1.51/1.73  thf('14', plain,
% 1.51/1.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf('15', plain,
% 1.51/1.73      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.51/1.73         (((k9_subset_1 @ X13 @ X11 @ X12) = (k3_xboole_0 @ X11 @ X12))
% 1.51/1.73          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 1.51/1.73      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.51/1.73  thf('16', plain,
% 1.51/1.73      (![X0 : $i]:
% 1.51/1.73         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 1.51/1.73           = (k3_xboole_0 @ X0 @ sk_B))),
% 1.51/1.73      inference('sup-', [status(thm)], ['14', '15'])).
% 1.51/1.73  thf('17', plain,
% 1.51/1.73      (![X0 : $i]:
% 1.51/1.73         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.51/1.73          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.51/1.73              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.51/1.73              = (k3_xboole_0 @ X0 @ sk_B)))),
% 1.51/1.73      inference('demod', [status(thm)], ['10', '13', '16'])).
% 1.51/1.73  thf('18', plain,
% 1.51/1.73      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 1.51/1.73         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.51/1.73         = (k3_xboole_0 @ sk_C @ sk_B))),
% 1.51/1.73      inference('sup-', [status(thm)], ['5', '17'])).
% 1.51/1.73  thf('19', plain,
% 1.51/1.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf(redefinition_k7_subset_1, axiom,
% 1.51/1.73    (![A:$i,B:$i,C:$i]:
% 1.51/1.73     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.51/1.73       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.51/1.73  thf('20', plain,
% 1.51/1.73      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.51/1.73         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 1.51/1.73          | ((k7_subset_1 @ X9 @ X8 @ X10) = (k4_xboole_0 @ X8 @ X10)))),
% 1.51/1.73      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.51/1.73  thf('21', plain,
% 1.51/1.73      (![X0 : $i]:
% 1.51/1.73         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)
% 1.51/1.73           = (k4_xboole_0 @ sk_C @ X0))),
% 1.51/1.73      inference('sup-', [status(thm)], ['19', '20'])).
% 1.51/1.73  thf(commutativity_k2_tarski, axiom,
% 1.51/1.73    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.51/1.73  thf('22', plain,
% 1.51/1.73      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 1.51/1.73      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.51/1.73  thf(t12_setfam_1, axiom,
% 1.51/1.73    (![A:$i,B:$i]:
% 1.51/1.73     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.51/1.73  thf('23', plain,
% 1.51/1.73      (![X17 : $i, X18 : $i]:
% 1.51/1.73         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 1.51/1.73      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.51/1.73  thf('24', plain,
% 1.51/1.73      (![X0 : $i, X1 : $i]:
% 1.51/1.73         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.51/1.73      inference('sup+', [status(thm)], ['22', '23'])).
% 1.51/1.73  thf('25', plain,
% 1.51/1.73      (![X17 : $i, X18 : $i]:
% 1.51/1.73         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 1.51/1.73      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.51/1.73  thf('26', plain,
% 1.51/1.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.51/1.73      inference('sup+', [status(thm)], ['24', '25'])).
% 1.51/1.73  thf('27', plain,
% 1.51/1.73      (((k4_xboole_0 @ sk_C @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.51/1.73         = (k3_xboole_0 @ sk_B @ sk_C))),
% 1.51/1.73      inference('demod', [status(thm)], ['18', '21', '26'])).
% 1.51/1.73  thf('28', plain,
% 1.51/1.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf(dt_k1_pre_topc, axiom,
% 1.51/1.73    (![A:$i,B:$i]:
% 1.51/1.73     ( ( ( l1_pre_topc @ A ) & 
% 1.51/1.73         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.51/1.73       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 1.51/1.73         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 1.51/1.73  thf('29', plain,
% 1.51/1.73      (![X22 : $i, X23 : $i]:
% 1.51/1.73         (~ (l1_pre_topc @ X22)
% 1.51/1.73          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.51/1.73          | (m1_pre_topc @ (k1_pre_topc @ X22 @ X23) @ X22))),
% 1.51/1.73      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 1.51/1.73  thf('30', plain,
% 1.51/1.73      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C) @ sk_A)
% 1.51/1.73        | ~ (l1_pre_topc @ sk_A))),
% 1.51/1.73      inference('sup-', [status(thm)], ['28', '29'])).
% 1.51/1.73  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf('32', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_C) @ sk_A)),
% 1.51/1.73      inference('demod', [status(thm)], ['30', '31'])).
% 1.51/1.73  thf(t36_xboole_1, axiom,
% 1.51/1.73    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.51/1.73  thf('33', plain,
% 1.51/1.73      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 1.51/1.73      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.51/1.73  thf(t3_subset, axiom,
% 1.51/1.73    (![A:$i,B:$i]:
% 1.51/1.73     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.51/1.73  thf('34', plain,
% 1.51/1.73      (![X19 : $i, X21 : $i]:
% 1.51/1.73         ((m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X19 @ X21))),
% 1.51/1.73      inference('cnf', [status(esa)], [t3_subset])).
% 1.51/1.73  thf('35', plain,
% 1.51/1.73      (![X0 : $i, X1 : $i]:
% 1.51/1.73         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.51/1.73      inference('sup-', [status(thm)], ['33', '34'])).
% 1.51/1.73  thf(t39_pre_topc, axiom,
% 1.51/1.73    (![A:$i]:
% 1.51/1.73     ( ( l1_pre_topc @ A ) =>
% 1.51/1.73       ( ![B:$i]:
% 1.51/1.73         ( ( m1_pre_topc @ B @ A ) =>
% 1.51/1.73           ( ![C:$i]:
% 1.51/1.73             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 1.51/1.73               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 1.51/1.73  thf('36', plain,
% 1.51/1.73      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.51/1.73         (~ (m1_pre_topc @ X26 @ X27)
% 1.51/1.73          | (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.51/1.73          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 1.51/1.73          | ~ (l1_pre_topc @ X27))),
% 1.51/1.73      inference('cnf', [status(esa)], [t39_pre_topc])).
% 1.51/1.73  thf('37', plain,
% 1.51/1.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.73         (~ (l1_pre_topc @ X2)
% 1.51/1.73          | (m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ 
% 1.51/1.73             (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 1.51/1.73          | ~ (m1_pre_topc @ X0 @ X2))),
% 1.51/1.73      inference('sup-', [status(thm)], ['35', '36'])).
% 1.51/1.73  thf('38', plain,
% 1.51/1.73      (![X0 : $i]:
% 1.51/1.73         ((m1_subset_1 @ 
% 1.51/1.73           (k4_xboole_0 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) @ X0) @ 
% 1.51/1.73           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.51/1.73          | ~ (l1_pre_topc @ sk_A))),
% 1.51/1.73      inference('sup-', [status(thm)], ['32', '37'])).
% 1.51/1.73  thf('39', plain,
% 1.51/1.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf(t29_pre_topc, axiom,
% 1.51/1.73    (![A:$i]:
% 1.51/1.73     ( ( l1_pre_topc @ A ) =>
% 1.51/1.73       ( ![B:$i]:
% 1.51/1.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.51/1.73           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 1.51/1.73  thf('40', plain,
% 1.51/1.73      (![X24 : $i, X25 : $i]:
% 1.51/1.73         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.51/1.73          | ((u1_struct_0 @ (k1_pre_topc @ X25 @ X24)) = (X24))
% 1.51/1.73          | ~ (l1_pre_topc @ X25))),
% 1.51/1.73      inference('cnf', [status(esa)], [t29_pre_topc])).
% 1.51/1.73  thf('41', plain,
% 1.51/1.73      ((~ (l1_pre_topc @ sk_A)
% 1.51/1.73        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) = (sk_C)))),
% 1.51/1.73      inference('sup-', [status(thm)], ['39', '40'])).
% 1.51/1.73  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf('43', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) = (sk_C))),
% 1.51/1.73      inference('demod', [status(thm)], ['41', '42'])).
% 1.51/1.73  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf('45', plain,
% 1.51/1.73      (![X0 : $i]:
% 1.51/1.73         (m1_subset_1 @ (k4_xboole_0 @ sk_C @ X0) @ 
% 1.51/1.73          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.73      inference('demod', [status(thm)], ['38', '43', '44'])).
% 1.51/1.73  thf('46', plain,
% 1.51/1.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf(t18_compts_1, axiom,
% 1.51/1.73    (![A:$i]:
% 1.51/1.73     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.51/1.73       ( ![B:$i]:
% 1.51/1.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.51/1.73           ( ![C:$i]:
% 1.51/1.73             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.51/1.73               ( ( ( v2_compts_1 @ B @ A ) & ( r1_tarski @ C @ B ) & 
% 1.51/1.73                   ( v4_pre_topc @ C @ A ) ) =>
% 1.51/1.73                 ( v2_compts_1 @ C @ A ) ) ) ) ) ) ))).
% 1.51/1.73  thf('47', plain,
% 1.51/1.73      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.51/1.73         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 1.51/1.73          | ~ (v2_compts_1 @ X34 @ X35)
% 1.51/1.73          | ~ (r1_tarski @ X36 @ X34)
% 1.51/1.73          | ~ (v4_pre_topc @ X36 @ X35)
% 1.51/1.73          | (v2_compts_1 @ X36 @ X35)
% 1.51/1.73          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 1.51/1.73          | ~ (l1_pre_topc @ X35)
% 1.51/1.73          | ~ (v2_pre_topc @ X35))),
% 1.51/1.73      inference('cnf', [status(esa)], [t18_compts_1])).
% 1.51/1.73  thf('48', plain,
% 1.51/1.73      (![X0 : $i]:
% 1.51/1.73         (~ (v2_pre_topc @ sk_A)
% 1.51/1.73          | ~ (l1_pre_topc @ sk_A)
% 1.51/1.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.51/1.73          | (v2_compts_1 @ X0 @ sk_A)
% 1.51/1.73          | ~ (v4_pre_topc @ X0 @ sk_A)
% 1.51/1.73          | ~ (r1_tarski @ X0 @ sk_C)
% 1.51/1.73          | ~ (v2_compts_1 @ sk_C @ sk_A))),
% 1.51/1.73      inference('sup-', [status(thm)], ['46', '47'])).
% 1.51/1.73  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf('51', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf('52', plain,
% 1.51/1.73      (![X0 : $i]:
% 1.51/1.73         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.51/1.73          | (v2_compts_1 @ X0 @ sk_A)
% 1.51/1.73          | ~ (v4_pre_topc @ X0 @ sk_A)
% 1.51/1.73          | ~ (r1_tarski @ X0 @ sk_C))),
% 1.51/1.73      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 1.51/1.73  thf('53', plain,
% 1.51/1.73      (![X0 : $i]:
% 1.51/1.73         (~ (r1_tarski @ (k4_xboole_0 @ sk_C @ X0) @ sk_C)
% 1.51/1.73          | ~ (v4_pre_topc @ (k4_xboole_0 @ sk_C @ X0) @ sk_A)
% 1.51/1.73          | (v2_compts_1 @ (k4_xboole_0 @ sk_C @ X0) @ sk_A))),
% 1.51/1.73      inference('sup-', [status(thm)], ['45', '52'])).
% 1.51/1.73  thf('54', plain,
% 1.51/1.73      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 1.51/1.73      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.51/1.73  thf('55', plain,
% 1.51/1.73      (![X0 : $i]:
% 1.51/1.73         (~ (v4_pre_topc @ (k4_xboole_0 @ sk_C @ X0) @ sk_A)
% 1.51/1.73          | (v2_compts_1 @ (k4_xboole_0 @ sk_C @ X0) @ sk_A))),
% 1.51/1.73      inference('demod', [status(thm)], ['53', '54'])).
% 1.51/1.73  thf('56', plain,
% 1.51/1.73      ((~ (v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)
% 1.51/1.73        | (v2_compts_1 @ 
% 1.51/1.73           (k4_xboole_0 @ sk_C @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.51/1.73           sk_A))),
% 1.51/1.73      inference('sup-', [status(thm)], ['27', '55'])).
% 1.51/1.73  thf('57', plain,
% 1.51/1.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf('58', plain,
% 1.51/1.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf(fc4_tops_1, axiom,
% 1.51/1.73    (![A:$i,B:$i,C:$i]:
% 1.51/1.73     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v4_pre_topc @ B @ A ) & 
% 1.51/1.73         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 1.51/1.73         ( v4_pre_topc @ C @ A ) & 
% 1.51/1.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.51/1.73       ( v4_pre_topc @ ( k3_xboole_0 @ B @ C ) @ A ) ))).
% 1.51/1.73  thf('59', plain,
% 1.51/1.73      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.51/1.73         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.51/1.73          | ~ (v4_pre_topc @ X29 @ X30)
% 1.51/1.73          | ~ (l1_pre_topc @ X30)
% 1.51/1.73          | ~ (v2_pre_topc @ X30)
% 1.51/1.73          | ~ (v4_pre_topc @ X31 @ X30)
% 1.51/1.73          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 1.51/1.73          | (v4_pre_topc @ (k3_xboole_0 @ X29 @ X31) @ X30))),
% 1.51/1.73      inference('cnf', [status(esa)], [fc4_tops_1])).
% 1.51/1.73  thf('60', plain,
% 1.51/1.73      (![X0 : $i]:
% 1.51/1.73         ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 1.51/1.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.51/1.73          | ~ (v4_pre_topc @ X0 @ sk_A)
% 1.51/1.73          | ~ (v2_pre_topc @ sk_A)
% 1.51/1.73          | ~ (l1_pre_topc @ sk_A)
% 1.51/1.73          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.51/1.73      inference('sup-', [status(thm)], ['58', '59'])).
% 1.51/1.73  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf('63', plain,
% 1.51/1.73      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf(t16_compts_1, axiom,
% 1.51/1.73    (![A:$i]:
% 1.51/1.73     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.51/1.73       ( ![B:$i]:
% 1.51/1.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.51/1.73           ( ( ( v8_pre_topc @ A ) & ( v2_compts_1 @ B @ A ) ) =>
% 1.51/1.73             ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 1.51/1.73  thf('64', plain,
% 1.51/1.73      (![X32 : $i, X33 : $i]:
% 1.51/1.73         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 1.51/1.73          | (v4_pre_topc @ X32 @ X33)
% 1.51/1.73          | ~ (v2_compts_1 @ X32 @ X33)
% 1.51/1.73          | ~ (v8_pre_topc @ X33)
% 1.51/1.73          | ~ (l1_pre_topc @ X33)
% 1.51/1.73          | ~ (v2_pre_topc @ X33))),
% 1.51/1.73      inference('cnf', [status(esa)], [t16_compts_1])).
% 1.51/1.73  thf('65', plain,
% 1.51/1.73      ((~ (v2_pre_topc @ sk_A)
% 1.51/1.73        | ~ (l1_pre_topc @ sk_A)
% 1.51/1.73        | ~ (v8_pre_topc @ sk_A)
% 1.51/1.73        | ~ (v2_compts_1 @ sk_B @ sk_A)
% 1.51/1.73        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.51/1.73      inference('sup-', [status(thm)], ['63', '64'])).
% 1.51/1.73  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf('68', plain, ((v8_pre_topc @ sk_A)),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf('69', plain, ((v2_compts_1 @ sk_B @ sk_A)),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf('70', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 1.51/1.73      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 1.51/1.73  thf('71', plain,
% 1.51/1.73      (![X0 : $i]:
% 1.51/1.73         ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 1.51/1.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.51/1.73          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 1.51/1.73      inference('demod', [status(thm)], ['60', '61', '62', '70'])).
% 1.51/1.73  thf('72', plain,
% 1.51/1.73      ((~ (v4_pre_topc @ sk_C @ sk_A)
% 1.51/1.73        | (v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A))),
% 1.51/1.73      inference('sup-', [status(thm)], ['57', '71'])).
% 1.51/1.73  thf('73', plain,
% 1.51/1.73      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf('74', plain,
% 1.51/1.73      (![X32 : $i, X33 : $i]:
% 1.51/1.73         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 1.51/1.73          | (v4_pre_topc @ X32 @ X33)
% 1.51/1.73          | ~ (v2_compts_1 @ X32 @ X33)
% 1.51/1.73          | ~ (v8_pre_topc @ X33)
% 1.51/1.73          | ~ (l1_pre_topc @ X33)
% 1.51/1.73          | ~ (v2_pre_topc @ X33))),
% 1.51/1.73      inference('cnf', [status(esa)], [t16_compts_1])).
% 1.51/1.73  thf('75', plain,
% 1.51/1.73      ((~ (v2_pre_topc @ sk_A)
% 1.51/1.73        | ~ (l1_pre_topc @ sk_A)
% 1.51/1.73        | ~ (v8_pre_topc @ sk_A)
% 1.51/1.73        | ~ (v2_compts_1 @ sk_C @ sk_A)
% 1.51/1.73        | (v4_pre_topc @ sk_C @ sk_A))),
% 1.51/1.73      inference('sup-', [status(thm)], ['73', '74'])).
% 1.51/1.73  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf('78', plain, ((v8_pre_topc @ sk_A)),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf('79', plain, ((v2_compts_1 @ sk_C @ sk_A)),
% 1.51/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.73  thf('80', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 1.51/1.73      inference('demod', [status(thm)], ['75', '76', '77', '78', '79'])).
% 1.51/1.73  thf('81', plain, ((v4_pre_topc @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 1.51/1.73      inference('demod', [status(thm)], ['72', '80'])).
% 1.51/1.73  thf('82', plain,
% 1.51/1.73      (((k4_xboole_0 @ sk_C @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.51/1.73         = (k3_xboole_0 @ sk_B @ sk_C))),
% 1.51/1.73      inference('demod', [status(thm)], ['18', '21', '26'])).
% 1.51/1.73  thf('83', plain, ((v2_compts_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 1.51/1.73      inference('demod', [status(thm)], ['56', '81', '82'])).
% 1.51/1.73  thf('84', plain, ($false), inference('demod', [status(thm)], ['4', '83'])).
% 1.51/1.73  
% 1.51/1.73  % SZS output end Refutation
% 1.51/1.73  
% 1.51/1.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
