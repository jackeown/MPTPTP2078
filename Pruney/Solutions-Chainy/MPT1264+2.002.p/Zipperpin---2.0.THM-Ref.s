%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q80WN5ZUoC

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 153 expanded)
%              Number of leaves         :   30 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :  815 (2076 expanded)
%              Number of equality atoms :   54 ( 113 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t81_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( v3_pre_topc @ C @ A )
                 => ( ( k2_pre_topc @ A @ C )
                    = ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v1_tops_1 @ B @ A )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( v3_pre_topc @ C @ A )
                   => ( ( k2_pre_topc @ A @ C )
                      = ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( v3_pre_topc @ B @ A )
               => ( ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) )
                  = ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X23 @ X24 )
      | ( ( k2_pre_topc @ X24 @ ( k9_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 @ ( k2_pre_topc @ X24 @ X25 ) ) )
        = ( k2_pre_topc @ X24 @ ( k9_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t41_tops_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('15',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('17',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k1_setfam_1 @ ( k2_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ X0 ) ) ) )
        = ( k2_pre_topc @ sk_A @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) ) ) ) ),
    inference(demod,[status(thm)],['3','4','5','14','15','16','17'])).

thf('19',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_setfam_1 @ ( k2_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['0','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v1_tops_1 @ X21 @ X22 )
      | ( ( k2_pre_topc @ X22 @ X21 )
        = ( k2_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('26',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('27',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('28',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['28'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('30',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('34',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('35',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('37',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( r2_hidden @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C ) ) )
      | ( r2_hidden @ ( sk_D @ sk_C @ sk_C @ X0 ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['28'])).

thf('41',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('43',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['28'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_C
      = ( k1_setfam_1 @ ( k2_tarski @ ( k2_struct_0 @ sk_A ) @ sk_C ) ) )
    | ( sk_C
      = ( k1_setfam_1 @ ( k2_tarski @ ( k2_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['39','47'])).

thf('49',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('50',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('51',plain,
    ( ( sk_C
      = ( k1_setfam_1 @ ( k2_tarski @ sk_C @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( sk_C
      = ( k1_setfam_1 @ ( k2_tarski @ sk_C @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,
    ( sk_C
    = ( k1_setfam_1 @ ( k2_tarski @ sk_C @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C )
    = ( k2_pre_topc @ sk_A @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['19','25','52'])).

thf('54',plain,(
    ( k2_pre_topc @ sk_A @ sk_C )
 != ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_subset_1 @ X16 @ X14 @ X15 )
        = ( k1_setfam_1 @ ( k2_tarski @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('59',plain,(
    ( k2_pre_topc @ sk_A @ sk_C )
 != ( k2_pre_topc @ sk_A @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['54','57','58'])).

thf('60',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['53','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Q80WN5ZUoC
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:02:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 116 iterations in 0.047s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.50  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.50  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.21/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.50  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(t81_tops_1, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50           ( ( v1_tops_1 @ B @ A ) =>
% 0.21/0.50             ( ![C:$i]:
% 0.21/0.50               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50                 ( ( v3_pre_topc @ C @ A ) =>
% 0.21/0.50                   ( ( k2_pre_topc @ A @ C ) =
% 0.21/0.50                     ( k2_pre_topc @
% 0.21/0.50                       A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50              ( ( v1_tops_1 @ B @ A ) =>
% 0.21/0.50                ( ![C:$i]:
% 0.21/0.50                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50                    ( ( v3_pre_topc @ C @ A ) =>
% 0.21/0.50                      ( ( k2_pre_topc @ A @ C ) =
% 0.21/0.50                        ( k2_pre_topc @
% 0.21/0.50                          A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t81_tops_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t41_tops_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50               ( ( v3_pre_topc @ B @ A ) =>
% 0.21/0.50                 ( ( k2_pre_topc @
% 0.21/0.50                     A @ 
% 0.21/0.50                     ( k9_subset_1 @
% 0.21/0.50                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) ) =
% 0.21/0.50                   ( k2_pre_topc @
% 0.21/0.50                     A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.50          | ~ (v3_pre_topc @ X23 @ X24)
% 0.21/0.50          | ((k2_pre_topc @ X24 @ 
% 0.21/0.50              (k9_subset_1 @ (u1_struct_0 @ X24) @ X23 @ 
% 0.21/0.50               (k2_pre_topc @ X24 @ X25)))
% 0.21/0.50              = (k2_pre_topc @ X24 @ 
% 0.21/0.50                 (k9_subset_1 @ (u1_struct_0 @ X24) @ X23 @ X25)))
% 0.21/0.50          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.50          | ~ (l1_pre_topc @ X24)
% 0.21/0.50          | ~ (v2_pre_topc @ X24))),
% 0.21/0.50      inference('cnf', [status(esa)], [t41_tops_1])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v2_pre_topc @ sk_A)
% 0.21/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50          | ((k2_pre_topc @ sk_A @ 
% 0.21/0.50              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.21/0.50               (k2_pre_topc @ sk_A @ X0)))
% 0.21/0.50              = (k2_pre_topc @ sk_A @ 
% 0.21/0.50                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)))
% 0.21/0.50          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(commutativity_k9_subset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.50         (((k9_subset_1 @ X8 @ X10 @ X9) = (k9_subset_1 @ X8 @ X9 @ X10))
% 0.21/0.50          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.21/0.50      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.21/0.50           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(redefinition_k9_subset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.50         (((k9_subset_1 @ X16 @ X14 @ X15) = (k3_xboole_0 @ X14 @ X15))
% 0.21/0.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.21/0.50      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.21/0.50  thf(t12_setfam_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X17 : $i, X18 : $i]:
% 0.21/0.50         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.50         (((k9_subset_1 @ X16 @ X14 @ X15)
% 0.21/0.50            = (k1_setfam_1 @ (k2_tarski @ X14 @ X15)))
% 0.21/0.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.21/0.50      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.21/0.50           = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['9', '12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k1_setfam_1 @ (k2_tarski @ X0 @ sk_C))
% 0.21/0.50           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['8', '13'])).
% 0.21/0.50  thf(commutativity_k2_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k1_setfam_1 @ (k2_tarski @ X0 @ sk_C))
% 0.21/0.50           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['8', '13'])).
% 0.21/0.50  thf('17', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.50          | ((k2_pre_topc @ sk_A @ 
% 0.21/0.50              (k1_setfam_1 @ (k2_tarski @ sk_C @ (k2_pre_topc @ sk_A @ X0))))
% 0.21/0.50              = (k2_pre_topc @ sk_A @ (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)))))),
% 0.21/0.50      inference('demod', [status(thm)], ['3', '4', '5', '14', '15', '16', '17'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (((k2_pre_topc @ sk_A @ 
% 0.21/0.50         (k1_setfam_1 @ (k2_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_B))))
% 0.21/0.50         = (k2_pre_topc @ sk_A @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d3_tops_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.50           ( ( v1_tops_1 @ B @ A ) <=>
% 0.21/0.50             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X21 : $i, X22 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.21/0.50          | ~ (v1_tops_1 @ X21 @ X22)
% 0.21/0.50          | ((k2_pre_topc @ X22 @ X21) = (k2_struct_0 @ X22))
% 0.21/0.50          | ~ (l1_pre_topc @ X22))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.50        | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 0.21/0.50        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('24', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('25', plain, (((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.21/0.50  thf(d4_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.21/0.50       ( ![D:$i]:
% 0.21/0.50         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.50           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.21/0.50         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.21/0.50          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.21/0.50          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (![X17 : $i, X18 : $i]:
% 0.21/0.50         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.21/0.50         (((X5) = (k1_setfam_1 @ (k2_tarski @ X1 @ X2)))
% 0.21/0.50          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.21/0.50          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.21/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.21/0.50          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.21/0.50      inference('eq_fact', [status(thm)], ['28'])).
% 0.21/0.50  thf(d3_struct_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X19 : $i]:
% 0.21/0.50         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.21/0.50        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup+', [status(thm)], ['30', '31'])).
% 0.21/0.50  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_l1_pre_topc, axiom,
% 0.21/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.50  thf('35', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['32', '35'])).
% 0.21/0.50  thf(l3_subset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X11 @ X12)
% 0.21/0.50          | (r2_hidden @ X11 @ X13)
% 0.21/0.50          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.21/0.50      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ X0 @ (k2_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((sk_C) = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C)))
% 0.21/0.50          | (r2_hidden @ (sk_D @ sk_C @ sk_C @ X0) @ (k2_struct_0 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['29', '38'])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.21/0.50          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.21/0.50      inference('eq_fact', [status(thm)], ['28'])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.21/0.50         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.21/0.50          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.21/0.50          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.21/0.50          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (![X17 : $i, X18 : $i]:
% 0.21/0.50         ((k1_setfam_1 @ (k2_tarski @ X17 @ X18)) = (k3_xboole_0 @ X17 @ X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.21/0.50         (((X5) = (k1_setfam_1 @ (k2_tarski @ X1 @ X2)))
% 0.21/0.50          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.21/0.50          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.21/0.50          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.21/0.50      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.21/0.50          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.21/0.50          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.21/0.50          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['40', '43'])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.21/0.50          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.21/0.50          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.21/0.50          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.21/0.50      inference('eq_fact', [status(thm)], ['28'])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.21/0.50          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.21/0.50      inference('clc', [status(thm)], ['45', '46'])).
% 0.21/0.50  thf('48', plain,
% 0.21/0.50      ((((sk_C) = (k1_setfam_1 @ (k2_tarski @ (k2_struct_0 @ sk_A) @ sk_C)))
% 0.21/0.50        | ((sk_C) = (k1_setfam_1 @ (k2_tarski @ (k2_struct_0 @ sk_A) @ sk_C))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['39', '47'])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      ((((sk_C) = (k1_setfam_1 @ (k2_tarski @ sk_C @ (k2_struct_0 @ sk_A))))
% 0.21/0.50        | ((sk_C) = (k1_setfam_1 @ (k2_tarski @ sk_C @ (k2_struct_0 @ sk_A)))))),
% 0.21/0.50      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      (((sk_C) = (k1_setfam_1 @ (k2_tarski @ sk_C @ (k2_struct_0 @ sk_A))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['51'])).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      (((k2_pre_topc @ sk_A @ sk_C)
% 0.21/0.50         = (k2_pre_topc @ sk_A @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C))))),
% 0.21/0.50      inference('demod', [status(thm)], ['19', '25', '52'])).
% 0.21/0.50  thf('54', plain,
% 0.21/0.50      (((k2_pre_topc @ sk_A @ sk_C)
% 0.21/0.50         != (k2_pre_topc @ sk_A @ 
% 0.21/0.50             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('55', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('56', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.50         (((k9_subset_1 @ X16 @ X14 @ X15)
% 0.21/0.50            = (k1_setfam_1 @ (k2_tarski @ X14 @ X15)))
% 0.21/0.50          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.21/0.50      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('57', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.21/0.50           = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.50  thf('58', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.50  thf('59', plain,
% 0.21/0.50      (((k2_pre_topc @ sk_A @ sk_C)
% 0.21/0.50         != (k2_pre_topc @ sk_A @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C))))),
% 0.21/0.50      inference('demod', [status(thm)], ['54', '57', '58'])).
% 0.21/0.50  thf('60', plain, ($false),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['53', '59'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
