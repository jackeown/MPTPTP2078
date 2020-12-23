%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cAyqDKwLzc

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:06 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 157 expanded)
%              Number of leaves         :   32 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  831 (2092 expanded)
%              Number of equality atoms :   54 ( 113 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v3_pre_topc @ X27 @ X28 )
      | ( ( k2_pre_topc @ X28 @ ( k9_subset_1 @ ( u1_struct_0 @ X28 ) @ X27 @ ( k2_pre_topc @ X28 @ X29 ) ) )
        = ( k2_pre_topc @ X28 @ ( k9_subset_1 @ ( u1_struct_0 @ X28 ) @ X27 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t41_tops_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( k2_pre_topc @ sk_A @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X12 @ X14 @ X13 )
        = ( k9_subset_1 @ X12 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k9_subset_1 @ X17 @ X15 @ X16 )
        = ( k3_xboole_0 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('12',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k9_subset_1 @ X17 @ X15 @ X16 )
        = ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C_1 ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C_1 ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('17',plain,(
    v3_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k1_setfam_1 @ ( k2_tarski @ sk_C_1 @ ( k2_pre_topc @ sk_A @ X0 ) ) ) )
        = ( k2_pre_topc @ sk_A @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C_1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['3','4','5','14','15','16','17'])).

thf('19',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_setfam_1 @ ( k2_tarski @ sk_C_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v1_tops_1 @ X25 @ X26 )
      | ( ( k2_pre_topc @ X26 @ X25 )
        = ( k2_struct_0 @ X26 ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
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
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('28',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
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
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('31',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
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
    ! [X24: $i] :
      ( ( l1_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('35',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('37',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    r1_tarski @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_C_1 ) ) )
      | ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_C_1 @ X0 ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['28'])).

thf('43',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('44',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('45',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['28'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_C_1
      = ( k1_setfam_1 @ ( k2_tarski @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) ) )
    | ( sk_C_1
      = ( k1_setfam_1 @ ( k2_tarski @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['41','49'])).

thf('51',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('52',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('53',plain,
    ( ( sk_C_1
      = ( k1_setfam_1 @ ( k2_tarski @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( sk_C_1
      = ( k1_setfam_1 @ ( k2_tarski @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( sk_C_1
    = ( k1_setfam_1 @ ( k2_tarski @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C_1 )
    = ( k2_pre_topc @ sk_A @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['19','25','54'])).

thf('56',plain,(
    ( k2_pre_topc @ sk_A @ sk_C_1 )
 != ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k9_subset_1 @ X17 @ X15 @ X16 )
        = ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('61',plain,(
    ( k2_pre_topc @ sk_A @ sk_C_1 )
 != ( k2_pre_topc @ sk_A @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['56','59','60'])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['55','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cAyqDKwLzc
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:55:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.07/1.25  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.07/1.25  % Solved by: fo/fo7.sh
% 1.07/1.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.25  % done 1265 iterations in 0.795s
% 1.07/1.25  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.07/1.25  % SZS output start Refutation
% 1.07/1.25  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.07/1.25  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.07/1.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.07/1.25  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.07/1.25  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.07/1.25  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.07/1.25  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.25  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.07/1.25  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.07/1.25  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.07/1.25  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.07/1.25  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 1.07/1.25  thf(sk_B_type, type, sk_B: $i).
% 1.07/1.25  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.07/1.25  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.07/1.25  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.07/1.25  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.07/1.25  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.07/1.25  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.07/1.25  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.07/1.25  thf(t81_tops_1, conjecture,
% 1.07/1.25    (![A:$i]:
% 1.07/1.25     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.07/1.25       ( ![B:$i]:
% 1.07/1.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.07/1.25           ( ( v1_tops_1 @ B @ A ) =>
% 1.07/1.25             ( ![C:$i]:
% 1.07/1.25               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.07/1.25                 ( ( v3_pre_topc @ C @ A ) =>
% 1.07/1.25                   ( ( k2_pre_topc @ A @ C ) =
% 1.07/1.25                     ( k2_pre_topc @
% 1.07/1.25                       A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ))).
% 1.07/1.25  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.25    (~( ![A:$i]:
% 1.07/1.25        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.07/1.25          ( ![B:$i]:
% 1.07/1.25            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.07/1.25              ( ( v1_tops_1 @ B @ A ) =>
% 1.07/1.25                ( ![C:$i]:
% 1.07/1.25                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.07/1.25                    ( ( v3_pre_topc @ C @ A ) =>
% 1.07/1.25                      ( ( k2_pre_topc @ A @ C ) =
% 1.07/1.25                        ( k2_pre_topc @
% 1.07/1.25                          A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ) )),
% 1.07/1.25    inference('cnf.neg', [status(esa)], [t81_tops_1])).
% 1.07/1.25  thf('0', plain,
% 1.07/1.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('1', plain,
% 1.07/1.25      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf(t41_tops_1, axiom,
% 1.07/1.25    (![A:$i]:
% 1.07/1.25     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.07/1.25       ( ![B:$i]:
% 1.07/1.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.07/1.25           ( ![C:$i]:
% 1.07/1.25             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.07/1.25               ( ( v3_pre_topc @ B @ A ) =>
% 1.07/1.25                 ( ( k2_pre_topc @
% 1.07/1.25                     A @ 
% 1.07/1.25                     ( k9_subset_1 @
% 1.07/1.25                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) ) =
% 1.07/1.25                   ( k2_pre_topc @
% 1.07/1.25                     A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) ))).
% 1.07/1.25  thf('2', plain,
% 1.07/1.25      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.07/1.25         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.07/1.25          | ~ (v3_pre_topc @ X27 @ X28)
% 1.07/1.25          | ((k2_pre_topc @ X28 @ 
% 1.07/1.25              (k9_subset_1 @ (u1_struct_0 @ X28) @ X27 @ 
% 1.07/1.25               (k2_pre_topc @ X28 @ X29)))
% 1.07/1.25              = (k2_pre_topc @ X28 @ 
% 1.07/1.25                 (k9_subset_1 @ (u1_struct_0 @ X28) @ X27 @ X29)))
% 1.07/1.25          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 1.07/1.25          | ~ (l1_pre_topc @ X28)
% 1.07/1.25          | ~ (v2_pre_topc @ X28))),
% 1.07/1.25      inference('cnf', [status(esa)], [t41_tops_1])).
% 1.07/1.25  thf('3', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         (~ (v2_pre_topc @ sk_A)
% 1.07/1.25          | ~ (l1_pre_topc @ sk_A)
% 1.07/1.25          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.07/1.25          | ((k2_pre_topc @ sk_A @ 
% 1.07/1.25              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 1.07/1.25               (k2_pre_topc @ sk_A @ X0)))
% 1.07/1.25              = (k2_pre_topc @ sk_A @ 
% 1.07/1.25                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0)))
% 1.07/1.25          | ~ (v3_pre_topc @ sk_C_1 @ sk_A))),
% 1.07/1.25      inference('sup-', [status(thm)], ['1', '2'])).
% 1.07/1.25  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('6', plain,
% 1.07/1.25      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf(commutativity_k9_subset_1, axiom,
% 1.07/1.25    (![A:$i,B:$i,C:$i]:
% 1.07/1.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.07/1.25       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 1.07/1.25  thf('7', plain,
% 1.07/1.25      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.07/1.25         (((k9_subset_1 @ X12 @ X14 @ X13) = (k9_subset_1 @ X12 @ X13 @ X14))
% 1.07/1.25          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 1.07/1.25      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 1.07/1.25  thf('8', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C_1)
% 1.07/1.25           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0))),
% 1.07/1.25      inference('sup-', [status(thm)], ['6', '7'])).
% 1.07/1.25  thf('9', plain,
% 1.07/1.25      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf(redefinition_k9_subset_1, axiom,
% 1.07/1.25    (![A:$i,B:$i,C:$i]:
% 1.07/1.25     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.07/1.25       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.07/1.25  thf('10', plain,
% 1.07/1.25      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.07/1.25         (((k9_subset_1 @ X17 @ X15 @ X16) = (k3_xboole_0 @ X15 @ X16))
% 1.07/1.25          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 1.07/1.25      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.07/1.25  thf(t12_setfam_1, axiom,
% 1.07/1.25    (![A:$i,B:$i]:
% 1.07/1.25     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.07/1.25  thf('11', plain,
% 1.07/1.25      (![X18 : $i, X19 : $i]:
% 1.07/1.25         ((k1_setfam_1 @ (k2_tarski @ X18 @ X19)) = (k3_xboole_0 @ X18 @ X19))),
% 1.07/1.25      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.07/1.25  thf('12', plain,
% 1.07/1.25      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.07/1.25         (((k9_subset_1 @ X17 @ X15 @ X16)
% 1.07/1.25            = (k1_setfam_1 @ (k2_tarski @ X15 @ X16)))
% 1.07/1.25          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 1.07/1.25      inference('demod', [status(thm)], ['10', '11'])).
% 1.07/1.25  thf('13', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C_1)
% 1.07/1.25           = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C_1)))),
% 1.07/1.25      inference('sup-', [status(thm)], ['9', '12'])).
% 1.07/1.25  thf('14', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         ((k1_setfam_1 @ (k2_tarski @ X0 @ sk_C_1))
% 1.07/1.25           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0))),
% 1.07/1.25      inference('demod', [status(thm)], ['8', '13'])).
% 1.07/1.25  thf(commutativity_k2_tarski, axiom,
% 1.07/1.25    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.07/1.25  thf('15', plain,
% 1.07/1.25      (![X10 : $i, X11 : $i]:
% 1.07/1.25         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 1.07/1.25      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.07/1.25  thf('16', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         ((k1_setfam_1 @ (k2_tarski @ X0 @ sk_C_1))
% 1.07/1.25           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0))),
% 1.07/1.25      inference('demod', [status(thm)], ['8', '13'])).
% 1.07/1.25  thf('17', plain, ((v3_pre_topc @ sk_C_1 @ sk_A)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('18', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.07/1.25          | ((k2_pre_topc @ sk_A @ 
% 1.07/1.25              (k1_setfam_1 @ (k2_tarski @ sk_C_1 @ (k2_pre_topc @ sk_A @ X0))))
% 1.07/1.25              = (k2_pre_topc @ sk_A @ (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C_1)))))),
% 1.07/1.25      inference('demod', [status(thm)], ['3', '4', '5', '14', '15', '16', '17'])).
% 1.07/1.25  thf('19', plain,
% 1.07/1.25      (((k2_pre_topc @ sk_A @ 
% 1.07/1.25         (k1_setfam_1 @ (k2_tarski @ sk_C_1 @ (k2_pre_topc @ sk_A @ sk_B))))
% 1.07/1.25         = (k2_pre_topc @ sk_A @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C_1))))),
% 1.07/1.25      inference('sup-', [status(thm)], ['0', '18'])).
% 1.07/1.25  thf('20', plain,
% 1.07/1.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf(d3_tops_1, axiom,
% 1.07/1.25    (![A:$i]:
% 1.07/1.25     ( ( l1_pre_topc @ A ) =>
% 1.07/1.25       ( ![B:$i]:
% 1.07/1.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.07/1.25           ( ( v1_tops_1 @ B @ A ) <=>
% 1.07/1.25             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 1.07/1.25  thf('21', plain,
% 1.07/1.25      (![X25 : $i, X26 : $i]:
% 1.07/1.25         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 1.07/1.25          | ~ (v1_tops_1 @ X25 @ X26)
% 1.07/1.25          | ((k2_pre_topc @ X26 @ X25) = (k2_struct_0 @ X26))
% 1.07/1.25          | ~ (l1_pre_topc @ X26))),
% 1.07/1.25      inference('cnf', [status(esa)], [d3_tops_1])).
% 1.07/1.25  thf('22', plain,
% 1.07/1.25      ((~ (l1_pre_topc @ sk_A)
% 1.07/1.25        | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 1.07/1.25        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 1.07/1.25      inference('sup-', [status(thm)], ['20', '21'])).
% 1.07/1.25  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('24', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('25', plain, (((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))),
% 1.07/1.25      inference('demod', [status(thm)], ['22', '23', '24'])).
% 1.07/1.25  thf(d4_xboole_0, axiom,
% 1.07/1.25    (![A:$i,B:$i,C:$i]:
% 1.07/1.25     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.07/1.25       ( ![D:$i]:
% 1.07/1.25         ( ( r2_hidden @ D @ C ) <=>
% 1.07/1.25           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.07/1.25  thf('26', plain,
% 1.07/1.25      (![X5 : $i, X6 : $i, X9 : $i]:
% 1.07/1.25         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 1.07/1.25          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 1.07/1.25          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 1.07/1.25      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.07/1.25  thf('27', plain,
% 1.07/1.25      (![X18 : $i, X19 : $i]:
% 1.07/1.25         ((k1_setfam_1 @ (k2_tarski @ X18 @ X19)) = (k3_xboole_0 @ X18 @ X19))),
% 1.07/1.25      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.07/1.25  thf('28', plain,
% 1.07/1.25      (![X5 : $i, X6 : $i, X9 : $i]:
% 1.07/1.25         (((X9) = (k1_setfam_1 @ (k2_tarski @ X5 @ X6)))
% 1.07/1.25          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 1.07/1.25          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 1.07/1.25      inference('demod', [status(thm)], ['26', '27'])).
% 1.07/1.25  thf('29', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]:
% 1.07/1.25         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.07/1.25          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 1.07/1.25      inference('eq_fact', [status(thm)], ['28'])).
% 1.07/1.25  thf(d3_struct_0, axiom,
% 1.07/1.25    (![A:$i]:
% 1.07/1.25     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.07/1.25  thf('30', plain,
% 1.07/1.25      (![X23 : $i]:
% 1.07/1.25         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.07/1.25      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.07/1.25  thf('31', plain,
% 1.07/1.25      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('32', plain,
% 1.07/1.25      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 1.07/1.25        | ~ (l1_struct_0 @ sk_A))),
% 1.07/1.25      inference('sup+', [status(thm)], ['30', '31'])).
% 1.07/1.25  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf(dt_l1_pre_topc, axiom,
% 1.07/1.25    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.07/1.25  thf('34', plain,
% 1.07/1.25      (![X24 : $i]: ((l1_struct_0 @ X24) | ~ (l1_pre_topc @ X24))),
% 1.07/1.25      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.07/1.25  thf('35', plain, ((l1_struct_0 @ sk_A)),
% 1.07/1.25      inference('sup-', [status(thm)], ['33', '34'])).
% 1.07/1.25  thf('36', plain,
% 1.07/1.25      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 1.07/1.25      inference('demod', [status(thm)], ['32', '35'])).
% 1.07/1.25  thf(t3_subset, axiom,
% 1.07/1.25    (![A:$i,B:$i]:
% 1.07/1.25     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.07/1.25  thf('37', plain,
% 1.07/1.25      (![X20 : $i, X21 : $i]:
% 1.07/1.25         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 1.07/1.25      inference('cnf', [status(esa)], [t3_subset])).
% 1.07/1.25  thf('38', plain, ((r1_tarski @ sk_C_1 @ (k2_struct_0 @ sk_A))),
% 1.07/1.25      inference('sup-', [status(thm)], ['36', '37'])).
% 1.07/1.25  thf(d3_tarski, axiom,
% 1.07/1.25    (![A:$i,B:$i]:
% 1.07/1.25     ( ( r1_tarski @ A @ B ) <=>
% 1.07/1.25       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.07/1.25  thf('39', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.25         (~ (r2_hidden @ X0 @ X1)
% 1.07/1.25          | (r2_hidden @ X0 @ X2)
% 1.07/1.25          | ~ (r1_tarski @ X1 @ X2))),
% 1.07/1.25      inference('cnf', [status(esa)], [d3_tarski])).
% 1.07/1.25  thf('40', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         ((r2_hidden @ X0 @ (k2_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 1.07/1.25      inference('sup-', [status(thm)], ['38', '39'])).
% 1.07/1.25  thf('41', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         (((sk_C_1) = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_C_1)))
% 1.07/1.25          | (r2_hidden @ (sk_D @ sk_C_1 @ sk_C_1 @ X0) @ (k2_struct_0 @ sk_A)))),
% 1.07/1.25      inference('sup-', [status(thm)], ['29', '40'])).
% 1.07/1.25  thf('42', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]:
% 1.07/1.25         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.07/1.25          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 1.07/1.25      inference('eq_fact', [status(thm)], ['28'])).
% 1.07/1.25  thf('43', plain,
% 1.07/1.25      (![X5 : $i, X6 : $i, X9 : $i]:
% 1.07/1.25         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 1.07/1.25          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 1.07/1.25          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 1.07/1.25          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 1.07/1.25      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.07/1.25  thf('44', plain,
% 1.07/1.25      (![X18 : $i, X19 : $i]:
% 1.07/1.25         ((k1_setfam_1 @ (k2_tarski @ X18 @ X19)) = (k3_xboole_0 @ X18 @ X19))),
% 1.07/1.25      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.07/1.25  thf('45', plain,
% 1.07/1.25      (![X5 : $i, X6 : $i, X9 : $i]:
% 1.07/1.25         (((X9) = (k1_setfam_1 @ (k2_tarski @ X5 @ X6)))
% 1.07/1.25          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 1.07/1.25          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 1.07/1.25          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 1.07/1.25      inference('demod', [status(thm)], ['43', '44'])).
% 1.07/1.25  thf('46', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]:
% 1.07/1.25         (((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 1.07/1.25          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.07/1.25          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.07/1.25          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 1.07/1.25      inference('sup-', [status(thm)], ['42', '45'])).
% 1.07/1.25  thf('47', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]:
% 1.07/1.25         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.07/1.25          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.07/1.25          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 1.07/1.25      inference('simplify', [status(thm)], ['46'])).
% 1.07/1.25  thf('48', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]:
% 1.07/1.25         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.07/1.25          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 1.07/1.25      inference('eq_fact', [status(thm)], ['28'])).
% 1.07/1.25  thf('49', plain,
% 1.07/1.25      (![X0 : $i, X1 : $i]:
% 1.07/1.25         (((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 1.07/1.25          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 1.07/1.25      inference('clc', [status(thm)], ['47', '48'])).
% 1.07/1.25  thf('50', plain,
% 1.07/1.25      ((((sk_C_1) = (k1_setfam_1 @ (k2_tarski @ (k2_struct_0 @ sk_A) @ sk_C_1)))
% 1.07/1.25        | ((sk_C_1)
% 1.07/1.25            = (k1_setfam_1 @ (k2_tarski @ (k2_struct_0 @ sk_A) @ sk_C_1))))),
% 1.07/1.25      inference('sup-', [status(thm)], ['41', '49'])).
% 1.07/1.25  thf('51', plain,
% 1.07/1.25      (![X10 : $i, X11 : $i]:
% 1.07/1.25         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 1.07/1.25      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.07/1.25  thf('52', plain,
% 1.07/1.25      (![X10 : $i, X11 : $i]:
% 1.07/1.25         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 1.07/1.25      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.07/1.25  thf('53', plain,
% 1.07/1.25      ((((sk_C_1) = (k1_setfam_1 @ (k2_tarski @ sk_C_1 @ (k2_struct_0 @ sk_A))))
% 1.07/1.25        | ((sk_C_1)
% 1.07/1.25            = (k1_setfam_1 @ (k2_tarski @ sk_C_1 @ (k2_struct_0 @ sk_A)))))),
% 1.07/1.25      inference('demod', [status(thm)], ['50', '51', '52'])).
% 1.07/1.25  thf('54', plain,
% 1.07/1.25      (((sk_C_1) = (k1_setfam_1 @ (k2_tarski @ sk_C_1 @ (k2_struct_0 @ sk_A))))),
% 1.07/1.25      inference('simplify', [status(thm)], ['53'])).
% 1.07/1.25  thf('55', plain,
% 1.07/1.25      (((k2_pre_topc @ sk_A @ sk_C_1)
% 1.07/1.25         = (k2_pre_topc @ sk_A @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C_1))))),
% 1.07/1.25      inference('demod', [status(thm)], ['19', '25', '54'])).
% 1.07/1.25  thf('56', plain,
% 1.07/1.25      (((k2_pre_topc @ sk_A @ sk_C_1)
% 1.07/1.25         != (k2_pre_topc @ sk_A @ 
% 1.07/1.25             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_B)))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('57', plain,
% 1.07/1.25      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.07/1.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.25  thf('58', plain,
% 1.07/1.25      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.07/1.25         (((k9_subset_1 @ X17 @ X15 @ X16)
% 1.07/1.25            = (k1_setfam_1 @ (k2_tarski @ X15 @ X16)))
% 1.07/1.25          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 1.07/1.25      inference('demod', [status(thm)], ['10', '11'])).
% 1.07/1.25  thf('59', plain,
% 1.07/1.25      (![X0 : $i]:
% 1.07/1.25         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 1.07/1.25           = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_B)))),
% 1.07/1.25      inference('sup-', [status(thm)], ['57', '58'])).
% 1.07/1.25  thf('60', plain,
% 1.07/1.25      (![X10 : $i, X11 : $i]:
% 1.07/1.25         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 1.07/1.25      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.07/1.25  thf('61', plain,
% 1.07/1.25      (((k2_pre_topc @ sk_A @ sk_C_1)
% 1.07/1.25         != (k2_pre_topc @ sk_A @ (k1_setfam_1 @ (k2_tarski @ sk_B @ sk_C_1))))),
% 1.07/1.25      inference('demod', [status(thm)], ['56', '59', '60'])).
% 1.07/1.25  thf('62', plain, ($false),
% 1.07/1.25      inference('simplify_reflect-', [status(thm)], ['55', '61'])).
% 1.07/1.25  
% 1.07/1.25  % SZS output end Refutation
% 1.07/1.25  
% 1.07/1.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
