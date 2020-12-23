%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZfClxSbLQG

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:31 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 226 expanded)
%              Number of leaves         :   29 (  79 expanded)
%              Depth                    :   15
%              Number of atoms          :  752 (2723 expanded)
%              Number of equality atoms :   47 ( 164 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t33_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v3_pre_topc @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                   => ( ( D = B )
                     => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_pre_topc @ C @ A )
               => ( ( v3_pre_topc @ B @ A )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                     => ( ( D = B )
                       => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_tops_2])).

thf('0',plain,(
    ~ ( v3_pre_topc @ sk_D_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_D_2 = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_D_2 = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X8 @ X10 @ X9 )
        = ( k9_subset_1 @ X8 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_subset_1 @ X16 @ X14 @ X15 )
        = ( k3_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_subset_1 @ X16 @ X14 @ X15 )
        = ( k1_setfam_1 @ ( k2_tarski @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ X0 @ sk_B )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_B ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf(t32_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( ( v3_pre_topc @ C @ B )
              <=> ? [D: $i] :
                    ( ( ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) )
                      = C )
                    & ( v3_pre_topc @ D @ A )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ X26 @ ( k2_struct_0 @ X23 ) )
       != X25 )
      | ~ ( v3_pre_topc @ X26 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v3_pre_topc @ X25 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t32_tops_2])).

thf('16',plain,(
    ! [X23: $i,X24: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ X26 @ ( k2_struct_0 @ X23 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ X26 @ ( k2_struct_0 @ X23 ) ) @ X23 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X26 @ X24 )
      | ~ ( m1_pre_topc @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_struct_0 @ sk_C ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ ( k2_struct_0 @ sk_C ) ) @ sk_C )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('19',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('20',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('21',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('25',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( r2_hidden @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_B ) ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['22'])).

thf('29',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('30',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('31',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['22'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B
      = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_C ) @ sk_B ) ) )
    | ( sk_B
      = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_C ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('38',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('39',plain,
    ( ( sk_B
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_C ) ) ) )
    | ( sk_B
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( sk_B
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( sk_B
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_struct_0 @ sk_C ) ) ) )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['19','40'])).

thf('42',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('43',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['44','45'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('47',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('48',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( sk_B
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['41','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_B ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_C ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('52',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('53',plain,
    ( sk_B
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['41','48'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v3_pre_topc @ sk_B @ sk_C )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18','49','50','51','52','53'])).

thf('55',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B @ sk_C )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['3','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v3_pre_topc @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['2','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZfClxSbLQG
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:22:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.35/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.52  % Solved by: fo/fo7.sh
% 0.35/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.52  % done 114 iterations in 0.071s
% 0.35/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.52  % SZS output start Refutation
% 0.35/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.52  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.35/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.35/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.35/0.52  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.35/0.52  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.35/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.35/0.52  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.35/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.35/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.52  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.35/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.52  thf(t33_tops_2, conjecture,
% 0.35/0.52    (![A:$i]:
% 0.35/0.52     ( ( l1_pre_topc @ A ) =>
% 0.35/0.52       ( ![B:$i]:
% 0.35/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.52           ( ![C:$i]:
% 0.35/0.52             ( ( m1_pre_topc @ C @ A ) =>
% 0.35/0.52               ( ( v3_pre_topc @ B @ A ) =>
% 0.35/0.52                 ( ![D:$i]:
% 0.35/0.52                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.35/0.52                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.52    (~( ![A:$i]:
% 0.35/0.52        ( ( l1_pre_topc @ A ) =>
% 0.35/0.52          ( ![B:$i]:
% 0.35/0.52            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.52              ( ![C:$i]:
% 0.35/0.52                ( ( m1_pre_topc @ C @ A ) =>
% 0.35/0.52                  ( ( v3_pre_topc @ B @ A ) =>
% 0.35/0.52                    ( ![D:$i]:
% 0.35/0.52                      ( ( m1_subset_1 @
% 0.35/0.52                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.35/0.52                        ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.35/0.52    inference('cnf.neg', [status(esa)], [t33_tops_2])).
% 0.35/0.52  thf('0', plain, (~ (v3_pre_topc @ sk_D_2 @ sk_C)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('1', plain, (((sk_D_2) = (sk_B))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('2', plain, (~ (v3_pre_topc @ sk_B @ sk_C)),
% 0.35/0.52      inference('demod', [status(thm)], ['0', '1'])).
% 0.35/0.52  thf('3', plain,
% 0.35/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('4', plain,
% 0.35/0.52      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('5', plain, (((sk_D_2) = (sk_B))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('6', plain,
% 0.35/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.35/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.35/0.52  thf(commutativity_k9_subset_1, axiom,
% 0.35/0.52    (![A:$i,B:$i,C:$i]:
% 0.35/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.52       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.35/0.52  thf('7', plain,
% 0.35/0.52      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.35/0.52         (((k9_subset_1 @ X8 @ X10 @ X9) = (k9_subset_1 @ X8 @ X9 @ X10))
% 0.35/0.52          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.35/0.52      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.35/0.52  thf('8', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         ((k9_subset_1 @ (u1_struct_0 @ sk_C) @ X0 @ sk_B)
% 0.35/0.52           = (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ X0))),
% 0.35/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.35/0.52  thf('9', plain,
% 0.35/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.35/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.35/0.52  thf(redefinition_k9_subset_1, axiom,
% 0.35/0.52    (![A:$i,B:$i,C:$i]:
% 0.35/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.52       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.35/0.52  thf('10', plain,
% 0.35/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.35/0.52         (((k9_subset_1 @ X16 @ X14 @ X15) = (k3_xboole_0 @ X14 @ X15))
% 0.35/0.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.35/0.52      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.35/0.52  thf(t12_setfam_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.35/0.52  thf('11', plain,
% 0.35/0.52      (![X17 : $i, X18 : $i]:
% 0.35/0.52         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 0.35/0.52      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.35/0.52  thf('12', plain,
% 0.35/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.35/0.52         (((k9_subset_1 @ X16 @ X14 @ X15)
% 0.35/0.52            = (k1_setfam_1 @ (k2_tarski @ X14 @ X15)))
% 0.35/0.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.35/0.52      inference('demod', [status(thm)], ['10', '11'])).
% 0.35/0.52  thf('13', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         ((k9_subset_1 @ (u1_struct_0 @ sk_C) @ X0 @ sk_B)
% 0.35/0.52           = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_B)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['9', '12'])).
% 0.35/0.52  thf('14', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         ((k1_setfam_1 @ (k2_tarski @ X0 @ sk_B))
% 0.35/0.52           = (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ X0))),
% 0.35/0.52      inference('demod', [status(thm)], ['8', '13'])).
% 0.35/0.53  thf(t32_tops_2, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( l1_pre_topc @ A ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.35/0.53           ( ![C:$i]:
% 0.35/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.35/0.53               ( ( v3_pre_topc @ C @ B ) <=>
% 0.35/0.53                 ( ?[D:$i]:
% 0.35/0.53                   ( ( ( k9_subset_1 @
% 0.35/0.53                         ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) =
% 0.35/0.53                       ( C ) ) & 
% 0.35/0.53                     ( v3_pre_topc @ D @ A ) & 
% 0.35/0.53                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.35/0.53  thf('15', plain,
% 0.35/0.53      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.35/0.53         (~ (m1_pre_topc @ X23 @ X24)
% 0.35/0.53          | ((k9_subset_1 @ (u1_struct_0 @ X23) @ X26 @ (k2_struct_0 @ X23))
% 0.35/0.53              != (X25))
% 0.35/0.53          | ~ (v3_pre_topc @ X26 @ X24)
% 0.35/0.53          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.35/0.53          | (v3_pre_topc @ X25 @ X23)
% 0.35/0.53          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.35/0.53          | ~ (l1_pre_topc @ X24))),
% 0.35/0.53      inference('cnf', [status(esa)], [t32_tops_2])).
% 0.35/0.53  thf('16', plain,
% 0.35/0.53      (![X23 : $i, X24 : $i, X26 : $i]:
% 0.35/0.53         (~ (l1_pre_topc @ X24)
% 0.35/0.53          | ~ (m1_subset_1 @ 
% 0.35/0.53               (k9_subset_1 @ (u1_struct_0 @ X23) @ X26 @ (k2_struct_0 @ X23)) @ 
% 0.35/0.53               (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.35/0.53          | (v3_pre_topc @ 
% 0.35/0.53             (k9_subset_1 @ (u1_struct_0 @ X23) @ X26 @ (k2_struct_0 @ X23)) @ 
% 0.35/0.53             X23)
% 0.35/0.53          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.35/0.53          | ~ (v3_pre_topc @ X26 @ X24)
% 0.35/0.53          | ~ (m1_pre_topc @ X23 @ X24))),
% 0.35/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.35/0.53  thf('17', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ 
% 0.35/0.53             (k1_setfam_1 @ (k2_tarski @ (k2_struct_0 @ sk_C) @ sk_B)) @ 
% 0.35/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))
% 0.35/0.53          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.35/0.53          | ~ (v3_pre_topc @ sk_B @ X0)
% 0.35/0.53          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.35/0.53          | (v3_pre_topc @ 
% 0.35/0.53             (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ (k2_struct_0 @ sk_C)) @ 
% 0.35/0.53             sk_C)
% 0.35/0.53          | ~ (l1_pre_topc @ X0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['14', '16'])).
% 0.35/0.53  thf(commutativity_k2_tarski, axiom,
% 0.35/0.53    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.35/0.53  thf('18', plain,
% 0.35/0.53      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.35/0.53      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.35/0.53  thf(d3_struct_0, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.35/0.53  thf('19', plain,
% 0.35/0.53      (![X19 : $i]:
% 0.35/0.53         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.35/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.35/0.53  thf(d4_xboole_0, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.35/0.53       ( ![D:$i]:
% 0.35/0.53         ( ( r2_hidden @ D @ C ) <=>
% 0.35/0.53           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.35/0.53  thf('20', plain,
% 0.35/0.53      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.35/0.53         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.35/0.53          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.35/0.53          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.35/0.53      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.35/0.53  thf('21', plain,
% 0.35/0.53      (![X17 : $i, X18 : $i]:
% 0.35/0.53         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 0.35/0.53      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.35/0.53  thf('22', plain,
% 0.35/0.53      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.35/0.53         (((X5) = (k1_setfam_1 @ (k2_tarski @ X1 @ X2)))
% 0.35/0.53          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.35/0.53          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.35/0.53      inference('demod', [status(thm)], ['20', '21'])).
% 0.35/0.53  thf('23', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.35/0.53          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.35/0.53      inference('eq_fact', [status(thm)], ['22'])).
% 0.35/0.53  thf('24', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.35/0.53      inference('demod', [status(thm)], ['4', '5'])).
% 0.35/0.53  thf(l3_subset_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.35/0.53  thf('25', plain,
% 0.35/0.53      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X11 @ X12)
% 0.35/0.53          | (r2_hidden @ X11 @ X13)
% 0.35/0.53          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.35/0.53      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.35/0.53  thf('26', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_C)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.35/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.35/0.53  thf('27', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (((sk_B) = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_B)))
% 0.35/0.53          | (r2_hidden @ (sk_D @ sk_B @ sk_B @ X0) @ (u1_struct_0 @ sk_C)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['23', '26'])).
% 0.35/0.53  thf('28', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.35/0.53          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.35/0.53      inference('eq_fact', [status(thm)], ['22'])).
% 0.35/0.53  thf('29', plain,
% 0.35/0.53      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.35/0.53         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.35/0.53          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.35/0.53          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.35/0.53          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.35/0.53      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.35/0.53  thf('30', plain,
% 0.35/0.53      (![X17 : $i, X18 : $i]:
% 0.35/0.53         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 0.35/0.53      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.35/0.53  thf('31', plain,
% 0.35/0.53      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.35/0.53         (((X5) = (k1_setfam_1 @ (k2_tarski @ X1 @ X2)))
% 0.35/0.53          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.35/0.53          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.35/0.53          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.35/0.53      inference('demod', [status(thm)], ['29', '30'])).
% 0.35/0.53  thf('32', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.35/0.53          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.35/0.53          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.35/0.53          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['28', '31'])).
% 0.35/0.53  thf('33', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.35/0.53          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.35/0.53          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.35/0.53      inference('simplify', [status(thm)], ['32'])).
% 0.35/0.53  thf('34', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.35/0.53          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.35/0.53      inference('eq_fact', [status(thm)], ['22'])).
% 0.35/0.53  thf('35', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.35/0.53          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.35/0.53      inference('clc', [status(thm)], ['33', '34'])).
% 0.35/0.53  thf('36', plain,
% 0.35/0.53      ((((sk_B) = (k1_setfam_1 @ (k2_tarski @ (u1_struct_0 @ sk_C) @ sk_B)))
% 0.35/0.53        | ((sk_B) = (k1_setfam_1 @ (k2_tarski @ (u1_struct_0 @ sk_C) @ sk_B))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['27', '35'])).
% 0.35/0.53  thf('37', plain,
% 0.35/0.53      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.35/0.53      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.35/0.53  thf('38', plain,
% 0.35/0.53      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.35/0.53      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.35/0.53  thf('39', plain,
% 0.35/0.53      ((((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_C))))
% 0.35/0.53        | ((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_C)))))),
% 0.35/0.53      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.35/0.53  thf('40', plain,
% 0.35/0.53      (((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_C))))),
% 0.35/0.53      inference('simplify', [status(thm)], ['39'])).
% 0.35/0.53  thf('41', plain,
% 0.35/0.53      ((((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_struct_0 @ sk_C))))
% 0.35/0.53        | ~ (l1_struct_0 @ sk_C))),
% 0.35/0.53      inference('sup+', [status(thm)], ['19', '40'])).
% 0.35/0.53  thf('42', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(dt_m1_pre_topc, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( l1_pre_topc @ A ) =>
% 0.35/0.53       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.35/0.53  thf('43', plain,
% 0.35/0.53      (![X21 : $i, X22 : $i]:
% 0.35/0.53         (~ (m1_pre_topc @ X21 @ X22)
% 0.35/0.53          | (l1_pre_topc @ X21)
% 0.35/0.53          | ~ (l1_pre_topc @ X22))),
% 0.35/0.53      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.35/0.53  thf('44', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.35/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.35/0.53  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('46', plain, ((l1_pre_topc @ sk_C)),
% 0.35/0.53      inference('demod', [status(thm)], ['44', '45'])).
% 0.35/0.53  thf(dt_l1_pre_topc, axiom,
% 0.35/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.35/0.53  thf('47', plain,
% 0.35/0.53      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.35/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.53  thf('48', plain, ((l1_struct_0 @ sk_C)),
% 0.35/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.35/0.53  thf('49', plain,
% 0.35/0.53      (((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_struct_0 @ sk_C))))),
% 0.35/0.53      inference('demod', [status(thm)], ['41', '48'])).
% 0.35/0.53  thf('50', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C)))),
% 0.35/0.53      inference('demod', [status(thm)], ['4', '5'])).
% 0.35/0.53  thf('51', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((k1_setfam_1 @ (k2_tarski @ X0 @ sk_B))
% 0.35/0.53           = (k9_subset_1 @ (u1_struct_0 @ sk_C) @ sk_B @ X0))),
% 0.35/0.53      inference('demod', [status(thm)], ['8', '13'])).
% 0.35/0.53  thf('52', plain,
% 0.35/0.53      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.35/0.53      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.35/0.53  thf('53', plain,
% 0.35/0.53      (((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_struct_0 @ sk_C))))),
% 0.35/0.53      inference('demod', [status(thm)], ['41', '48'])).
% 0.35/0.53  thf('54', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         (~ (m1_pre_topc @ sk_C @ X0)
% 0.35/0.53          | ~ (v3_pre_topc @ sk_B @ X0)
% 0.35/0.53          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.35/0.53          | (v3_pre_topc @ sk_B @ sk_C)
% 0.35/0.53          | ~ (l1_pre_topc @ X0))),
% 0.35/0.53      inference('demod', [status(thm)],
% 0.35/0.53                ['17', '18', '49', '50', '51', '52', '53'])).
% 0.35/0.53  thf('55', plain,
% 0.35/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.53        | (v3_pre_topc @ sk_B @ sk_C)
% 0.35/0.53        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.35/0.53        | ~ (m1_pre_topc @ sk_C @ sk_A))),
% 0.35/0.53      inference('sup-', [status(thm)], ['3', '54'])).
% 0.35/0.53  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('57', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('58', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('59', plain, ((v3_pre_topc @ sk_B @ sk_C)),
% 0.35/0.53      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.35/0.53  thf('60', plain, ($false), inference('demod', [status(thm)], ['2', '59'])).
% 0.35/0.53  
% 0.35/0.53  % SZS output end Refutation
% 0.35/0.53  
% 0.35/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
