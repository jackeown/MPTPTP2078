%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r6VD7Ab1lz

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:42 EST 2020

% Result     : Theorem 1.73s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :  180 (2597 expanded)
%              Number of leaves         :   37 ( 819 expanded)
%              Depth                    :   27
%              Number of atoms          : 1599 (24793 expanded)
%              Number of equality atoms :   98 (1492 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(t29_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_tops_1])).

thf('0',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X15 ) @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('4',plain,(
    ! [X12: $i] :
      ( ( k2_subset_1 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('5',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('7',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( ( k7_subset_1 @ X25 @ X26 @ X24 )
        = ( k9_subset_1 @ X25 @ X26 @ ( k3_subset_1 @ X25 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X13 @ X14 )
        = ( k4_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('11',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('16',plain,(
    ! [X32: $i] :
      ( ( l1_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X13 @ X14 )
        = ( k4_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('20',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('22',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('23',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('25',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('27',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['11','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['8','27'])).

thf('29',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('30',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('32',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('35',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ( r2_hidden @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('39',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('40',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X2 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_B
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('43',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('44',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('46',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('48',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('49',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('52',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('53',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('54',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ) )
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ) )
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('56',plain,
    ( ( sk_B
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['41','54','55'])).

thf('57',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_B @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_B @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
    | ~ ( l1_struct_0 @ sk_A )
    | ( sk_B
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['29','57'])).

thf('59',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('60',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_B @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ X1 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['32'])).

thf('62',plain,
    ( sk_B
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('64',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('65',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('66',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k1_setfam_1 @ ( k2_tarski @ X6 @ X7 ) ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['63','66'])).

thf('68',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['62','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['28','68'])).

thf('70',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('72',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('73',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['11','26'])).

thf('75',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['62','67'])).

thf('77',plain,(
    m1_subset_1 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('78',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k9_subset_1 @ X23 @ X21 @ X22 )
        = ( k3_xboole_0 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('79',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X27 @ X28 ) )
      = ( k3_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('80',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k9_subset_1 @ X23 @ X21 @ X22 )
        = ( k1_setfam_1 @ ( k2_tarski @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['70','81'])).

thf('83',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('84',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('85',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X8 @ X9 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('89',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
    = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ) )
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('91',plain,
    ( sk_B
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('92',plain,
    ( sk_B
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['62','67'])).

thf('94',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['89','92','93'])).

thf('95',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('96',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['62','67'])).

thf('97',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['94','97'])).

thf('99',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['82','98'])).

thf('100',plain,
    ( ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['2','99'])).

thf('101',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('102',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['103'])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('106',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v4_pre_topc @ X30 @ X31 )
      | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X31 ) @ ( k2_struct_0 @ X31 ) @ X30 ) @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('107',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['104','109'])).

thf('111',plain,
    ( ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['102','110'])).

thf('112',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['62','67'])).

thf('113',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('114',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('115',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('116',plain,
    ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['113','116'])).

thf('118',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('119',plain,
    ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ~ ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['112','119'])).

thf('121',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['111','120'])).

thf('122',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['103'])).

thf('123',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['62','67'])).

thf('124',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('125',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('126',plain,
    ( ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['103'])).

thf('127',plain,
    ( ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['124','127'])).

thf('129',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('130',plain,
    ( ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['123','130'])).

thf('132',plain,
    ( ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('133',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X31 ) @ ( k2_struct_0 @ X31 ) @ X30 ) @ X31 )
      | ( v4_pre_topc @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('134',plain,
    ( ~ ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ~ ( v3_pre_topc @ ( k5_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['134','135','136'])).

thf('138',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['131','137'])).

thf('139',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('140',plain,
    ( ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','121','122','140'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.r6VD7Ab1lz
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.73/1.92  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.73/1.92  % Solved by: fo/fo7.sh
% 1.73/1.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.73/1.92  % done 1275 iterations in 1.457s
% 1.73/1.92  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.73/1.92  % SZS output start Refutation
% 1.73/1.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.73/1.92  thf(sk_B_type, type, sk_B: $i).
% 1.73/1.92  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.73/1.92  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.73/1.92  thf(sk_A_type, type, sk_A: $i).
% 1.73/1.92  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.73/1.92  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.73/1.92  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.73/1.92  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.73/1.92  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.73/1.92  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.73/1.92  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.73/1.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.73/1.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.73/1.92  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.73/1.92  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.73/1.92  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.73/1.92  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.73/1.92  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.73/1.92  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.73/1.92  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.73/1.92  thf(t29_tops_1, conjecture,
% 1.73/1.92    (![A:$i]:
% 1.73/1.92     ( ( l1_pre_topc @ A ) =>
% 1.73/1.92       ( ![B:$i]:
% 1.73/1.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.73/1.92           ( ( v4_pre_topc @ B @ A ) <=>
% 1.73/1.92             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 1.73/1.92  thf(zf_stmt_0, negated_conjecture,
% 1.73/1.92    (~( ![A:$i]:
% 1.73/1.92        ( ( l1_pre_topc @ A ) =>
% 1.73/1.92          ( ![B:$i]:
% 1.73/1.92            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.73/1.92              ( ( v4_pre_topc @ B @ A ) <=>
% 1.73/1.92                ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 1.73/1.92    inference('cnf.neg', [status(esa)], [t29_tops_1])).
% 1.73/1.92  thf('0', plain,
% 1.73/1.92      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.73/1.92        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('1', plain,
% 1.73/1.92      (~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 1.73/1.92       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.73/1.92      inference('split', [status(esa)], ['0'])).
% 1.73/1.92  thf(d3_struct_0, axiom,
% 1.73/1.92    (![A:$i]:
% 1.73/1.92     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.73/1.92  thf('2', plain,
% 1.73/1.92      (![X29 : $i]:
% 1.73/1.92         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.73/1.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.73/1.92  thf(dt_k2_subset_1, axiom,
% 1.73/1.92    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.73/1.92  thf('3', plain,
% 1.73/1.92      (![X15 : $i]: (m1_subset_1 @ (k2_subset_1 @ X15) @ (k1_zfmisc_1 @ X15))),
% 1.73/1.92      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 1.73/1.92  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.73/1.92  thf('4', plain, (![X12 : $i]: ((k2_subset_1 @ X12) = (X12))),
% 1.73/1.92      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.73/1.92  thf('5', plain, (![X15 : $i]: (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X15))),
% 1.73/1.92      inference('demod', [status(thm)], ['3', '4'])).
% 1.73/1.92  thf('6', plain,
% 1.73/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf(t32_subset_1, axiom,
% 1.73/1.92    (![A:$i,B:$i]:
% 1.73/1.92     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.73/1.92       ( ![C:$i]:
% 1.73/1.92         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.73/1.92           ( ( k7_subset_1 @ A @ B @ C ) =
% 1.73/1.92             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 1.73/1.92  thf('7', plain,
% 1.73/1.92      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.73/1.92         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 1.73/1.92          | ((k7_subset_1 @ X25 @ X26 @ X24)
% 1.73/1.92              = (k9_subset_1 @ X25 @ X26 @ (k3_subset_1 @ X25 @ X24)))
% 1.73/1.92          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 1.73/1.92      inference('cnf', [status(esa)], [t32_subset_1])).
% 1.73/1.92  thf('8', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.73/1.92          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 1.73/1.92              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.73/1.92                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 1.73/1.92      inference('sup-', [status(thm)], ['6', '7'])).
% 1.73/1.92  thf('9', plain,
% 1.73/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf(d5_subset_1, axiom,
% 1.73/1.92    (![A:$i,B:$i]:
% 1.73/1.92     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.73/1.92       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.73/1.92  thf('10', plain,
% 1.73/1.92      (![X13 : $i, X14 : $i]:
% 1.73/1.92         (((k3_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))
% 1.73/1.92          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 1.73/1.92      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.73/1.92  thf('11', plain,
% 1.73/1.92      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.73/1.92      inference('sup-', [status(thm)], ['9', '10'])).
% 1.73/1.92  thf('12', plain,
% 1.73/1.92      (![X29 : $i]:
% 1.73/1.92         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.73/1.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.73/1.92  thf('13', plain,
% 1.73/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('14', plain,
% 1.73/1.92      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 1.73/1.92        | ~ (l1_struct_0 @ sk_A))),
% 1.73/1.92      inference('sup+', [status(thm)], ['12', '13'])).
% 1.73/1.92  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf(dt_l1_pre_topc, axiom,
% 1.73/1.92    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.73/1.92  thf('16', plain,
% 1.73/1.92      (![X32 : $i]: ((l1_struct_0 @ X32) | ~ (l1_pre_topc @ X32))),
% 1.73/1.92      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.73/1.92  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 1.73/1.92      inference('sup-', [status(thm)], ['15', '16'])).
% 1.73/1.92  thf('18', plain,
% 1.73/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 1.73/1.92      inference('demod', [status(thm)], ['14', '17'])).
% 1.73/1.92  thf('19', plain,
% 1.73/1.92      (![X13 : $i, X14 : $i]:
% 1.73/1.92         (((k3_subset_1 @ X13 @ X14) = (k4_xboole_0 @ X13 @ X14))
% 1.73/1.92          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 1.73/1.92      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.73/1.92  thf('20', plain,
% 1.73/1.92      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.73/1.92      inference('sup-', [status(thm)], ['18', '19'])).
% 1.73/1.92  thf('21', plain,
% 1.73/1.92      (![X29 : $i]:
% 1.73/1.92         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.73/1.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.73/1.92  thf('22', plain,
% 1.73/1.92      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.73/1.92      inference('sup-', [status(thm)], ['9', '10'])).
% 1.73/1.92  thf('23', plain,
% 1.73/1.92      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.73/1.92        | ~ (l1_struct_0 @ sk_A))),
% 1.73/1.92      inference('sup+', [status(thm)], ['21', '22'])).
% 1.73/1.92  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 1.73/1.92      inference('sup-', [status(thm)], ['15', '16'])).
% 1.73/1.92  thf('25', plain,
% 1.73/1.92      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.73/1.92      inference('demod', [status(thm)], ['23', '24'])).
% 1.73/1.92  thf('26', plain,
% 1.73/1.92      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.73/1.92      inference('sup+', [status(thm)], ['20', '25'])).
% 1.73/1.92  thf('27', plain,
% 1.73/1.92      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.73/1.92      inference('demod', [status(thm)], ['11', '26'])).
% 1.73/1.92  thf('28', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.73/1.92          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 1.73/1.92              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.73/1.92                 (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.73/1.92      inference('demod', [status(thm)], ['8', '27'])).
% 1.73/1.92  thf('29', plain,
% 1.73/1.92      (![X29 : $i]:
% 1.73/1.92         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.73/1.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.73/1.92  thf(d4_xboole_0, axiom,
% 1.73/1.92    (![A:$i,B:$i,C:$i]:
% 1.73/1.92     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.73/1.92       ( ![D:$i]:
% 1.73/1.92         ( ( r2_hidden @ D @ C ) <=>
% 1.73/1.92           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.73/1.92  thf('30', plain,
% 1.73/1.92      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.73/1.92         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 1.73/1.92          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.73/1.92          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.73/1.92      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.73/1.92  thf(t12_setfam_1, axiom,
% 1.73/1.92    (![A:$i,B:$i]:
% 1.73/1.92     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.73/1.92  thf('31', plain,
% 1.73/1.92      (![X27 : $i, X28 : $i]:
% 1.73/1.92         ((k1_setfam_1 @ (k2_tarski @ X27 @ X28)) = (k3_xboole_0 @ X27 @ X28))),
% 1.73/1.92      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.73/1.92  thf('32', plain,
% 1.73/1.92      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.73/1.92         (((X5) = (k1_setfam_1 @ (k2_tarski @ X1 @ X2)))
% 1.73/1.92          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.73/1.92          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.73/1.92      inference('demod', [status(thm)], ['30', '31'])).
% 1.73/1.92  thf('33', plain,
% 1.73/1.92      (![X0 : $i, X1 : $i]:
% 1.73/1.92         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.73/1.92          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 1.73/1.92      inference('eq_fact', [status(thm)], ['32'])).
% 1.73/1.92  thf('34', plain,
% 1.73/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf(l3_subset_1, axiom,
% 1.73/1.92    (![A:$i,B:$i]:
% 1.73/1.92     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.73/1.92       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 1.73/1.92  thf('35', plain,
% 1.73/1.92      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.73/1.92         (~ (r2_hidden @ X18 @ X19)
% 1.73/1.92          | (r2_hidden @ X18 @ X20)
% 1.73/1.92          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 1.73/1.92      inference('cnf', [status(esa)], [l3_subset_1])).
% 1.73/1.92  thf('36', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 1.73/1.92      inference('sup-', [status(thm)], ['34', '35'])).
% 1.73/1.92  thf('37', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         (((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ X0)))
% 1.73/1.92          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['33', '36'])).
% 1.73/1.92  thf('38', plain,
% 1.73/1.92      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.73/1.92         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 1.73/1.92          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.73/1.92          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.73/1.92          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.73/1.92      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.73/1.92  thf('39', plain,
% 1.73/1.92      (![X27 : $i, X28 : $i]:
% 1.73/1.92         ((k1_setfam_1 @ (k2_tarski @ X27 @ X28)) = (k3_xboole_0 @ X27 @ X28))),
% 1.73/1.92      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.73/1.92  thf('40', plain,
% 1.73/1.92      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.73/1.92         (((X5) = (k1_setfam_1 @ (k2_tarski @ X1 @ X2)))
% 1.73/1.92          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.73/1.92          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.73/1.92          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.73/1.92      inference('demod', [status(thm)], ['38', '39'])).
% 1.73/1.92  thf('41', plain,
% 1.73/1.92      ((((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))))
% 1.73/1.92        | ~ (r2_hidden @ (sk_D @ sk_B @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 1.73/1.92        | ~ (r2_hidden @ (sk_D @ sk_B @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 1.73/1.92        | ((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A)))))),
% 1.73/1.92      inference('sup-', [status(thm)], ['37', '40'])).
% 1.73/1.92  thf('42', plain,
% 1.73/1.92      (![X29 : $i]:
% 1.73/1.92         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.73/1.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.73/1.92  thf('43', plain,
% 1.73/1.92      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.73/1.92      inference('sup+', [status(thm)], ['20', '25'])).
% 1.73/1.92  thf(t48_xboole_1, axiom,
% 1.73/1.92    (![A:$i,B:$i]:
% 1.73/1.92     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.73/1.92  thf('44', plain,
% 1.73/1.92      (![X8 : $i, X9 : $i]:
% 1.73/1.92         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 1.73/1.92           = (k3_xboole_0 @ X8 @ X9))),
% 1.73/1.92      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.73/1.92  thf('45', plain,
% 1.73/1.92      (![X27 : $i, X28 : $i]:
% 1.73/1.92         ((k1_setfam_1 @ (k2_tarski @ X27 @ X28)) = (k3_xboole_0 @ X27 @ X28))),
% 1.73/1.92      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.73/1.92  thf('46', plain,
% 1.73/1.92      (![X8 : $i, X9 : $i]:
% 1.73/1.92         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 1.73/1.92           = (k1_setfam_1 @ (k2_tarski @ X8 @ X9)))),
% 1.73/1.92      inference('demod', [status(thm)], ['44', '45'])).
% 1.73/1.92  thf('47', plain,
% 1.73/1.92      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92         (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.73/1.92         = (k1_setfam_1 @ (k2_tarski @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 1.73/1.92      inference('sup+', [status(thm)], ['43', '46'])).
% 1.73/1.92  thf(commutativity_k2_tarski, axiom,
% 1.73/1.92    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.73/1.92  thf('48', plain,
% 1.73/1.92      (![X10 : $i, X11 : $i]:
% 1.73/1.92         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 1.73/1.92      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.73/1.92  thf('49', plain,
% 1.73/1.92      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92         (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.73/1.92         = (k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))))),
% 1.73/1.92      inference('demod', [status(thm)], ['47', '48'])).
% 1.73/1.92  thf('50', plain,
% 1.73/1.92      ((((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 1.73/1.92          (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.73/1.92          = (k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))))
% 1.73/1.92        | ~ (l1_struct_0 @ sk_A))),
% 1.73/1.92      inference('sup+', [status(thm)], ['42', '49'])).
% 1.73/1.92  thf('51', plain,
% 1.73/1.92      (![X8 : $i, X9 : $i]:
% 1.73/1.92         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 1.73/1.92           = (k1_setfam_1 @ (k2_tarski @ X8 @ X9)))),
% 1.73/1.92      inference('demod', [status(thm)], ['44', '45'])).
% 1.73/1.92  thf('52', plain,
% 1.73/1.92      (![X10 : $i, X11 : $i]:
% 1.73/1.92         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 1.73/1.92      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.73/1.92  thf('53', plain, ((l1_struct_0 @ sk_A)),
% 1.73/1.92      inference('sup-', [status(thm)], ['15', '16'])).
% 1.73/1.92  thf('54', plain,
% 1.73/1.92      (((k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_struct_0 @ sk_A)))
% 1.73/1.92         = (k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))))),
% 1.73/1.92      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 1.73/1.92  thf('55', plain,
% 1.73/1.92      (((k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_struct_0 @ sk_A)))
% 1.73/1.92         = (k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))))),
% 1.73/1.92      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 1.73/1.92  thf('56', plain,
% 1.73/1.92      ((((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_struct_0 @ sk_A))))
% 1.73/1.92        | ~ (r2_hidden @ (sk_D @ sk_B @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 1.73/1.92        | ~ (r2_hidden @ (sk_D @ sk_B @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 1.73/1.92        | ((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_struct_0 @ sk_A)))))),
% 1.73/1.92      inference('demod', [status(thm)], ['41', '54', '55'])).
% 1.73/1.92  thf('57', plain,
% 1.73/1.92      ((~ (r2_hidden @ (sk_D @ sk_B @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 1.73/1.92        | ((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_struct_0 @ sk_A)))))),
% 1.73/1.92      inference('simplify', [status(thm)], ['56'])).
% 1.73/1.92  thf('58', plain,
% 1.73/1.92      ((~ (r2_hidden @ (sk_D @ sk_B @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 1.73/1.92        | ~ (l1_struct_0 @ sk_A)
% 1.73/1.92        | ((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_struct_0 @ sk_A)))))),
% 1.73/1.92      inference('sup-', [status(thm)], ['29', '57'])).
% 1.73/1.92  thf('59', plain, ((l1_struct_0 @ sk_A)),
% 1.73/1.92      inference('sup-', [status(thm)], ['15', '16'])).
% 1.73/1.92  thf('60', plain,
% 1.73/1.92      ((~ (r2_hidden @ (sk_D @ sk_B @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 1.73/1.92        | ((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_struct_0 @ sk_A)))))),
% 1.73/1.92      inference('demod', [status(thm)], ['58', '59'])).
% 1.73/1.92  thf('61', plain,
% 1.73/1.92      (![X0 : $i, X1 : $i]:
% 1.73/1.92         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.73/1.92          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X0 @ X1))))),
% 1.73/1.92      inference('eq_fact', [status(thm)], ['32'])).
% 1.73/1.92  thf('62', plain,
% 1.73/1.92      (((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_struct_0 @ sk_A))))),
% 1.73/1.92      inference('clc', [status(thm)], ['60', '61'])).
% 1.73/1.92  thf('63', plain,
% 1.73/1.92      (![X10 : $i, X11 : $i]:
% 1.73/1.92         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 1.73/1.92      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.73/1.92  thf(t100_xboole_1, axiom,
% 1.73/1.92    (![A:$i,B:$i]:
% 1.73/1.92     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.73/1.92  thf('64', plain,
% 1.73/1.92      (![X6 : $i, X7 : $i]:
% 1.73/1.92         ((k4_xboole_0 @ X6 @ X7)
% 1.73/1.92           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 1.73/1.92      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.73/1.92  thf('65', plain,
% 1.73/1.92      (![X27 : $i, X28 : $i]:
% 1.73/1.92         ((k1_setfam_1 @ (k2_tarski @ X27 @ X28)) = (k3_xboole_0 @ X27 @ X28))),
% 1.73/1.92      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.73/1.92  thf('66', plain,
% 1.73/1.92      (![X6 : $i, X7 : $i]:
% 1.73/1.92         ((k4_xboole_0 @ X6 @ X7)
% 1.73/1.92           = (k5_xboole_0 @ X6 @ (k1_setfam_1 @ (k2_tarski @ X6 @ X7))))),
% 1.73/1.92      inference('demod', [status(thm)], ['64', '65'])).
% 1.73/1.92  thf('67', plain,
% 1.73/1.92      (![X0 : $i, X1 : $i]:
% 1.73/1.92         ((k4_xboole_0 @ X0 @ X1)
% 1.73/1.92           = (k5_xboole_0 @ X0 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 1.73/1.92      inference('sup+', [status(thm)], ['63', '66'])).
% 1.73/1.92  thf('68', plain,
% 1.73/1.92      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.73/1.92      inference('sup+', [status(thm)], ['62', '67'])).
% 1.73/1.92  thf('69', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.73/1.92          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 1.73/1.92              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.73/1.92                 (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.73/1.92      inference('demod', [status(thm)], ['28', '68'])).
% 1.73/1.92  thf('70', plain,
% 1.73/1.92      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92            (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['5', '69'])).
% 1.73/1.92  thf('71', plain,
% 1.73/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf(dt_k3_subset_1, axiom,
% 1.73/1.92    (![A:$i,B:$i]:
% 1.73/1.92     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.73/1.92       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.73/1.92  thf('72', plain,
% 1.73/1.92      (![X16 : $i, X17 : $i]:
% 1.73/1.92         ((m1_subset_1 @ (k3_subset_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16))
% 1.73/1.92          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 1.73/1.92      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.73/1.92  thf('73', plain,
% 1.73/1.92      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.73/1.92        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['71', '72'])).
% 1.73/1.92  thf('74', plain,
% 1.73/1.92      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.73/1.92      inference('demod', [status(thm)], ['11', '26'])).
% 1.73/1.92  thf('75', plain,
% 1.73/1.92      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 1.73/1.92        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('demod', [status(thm)], ['73', '74'])).
% 1.73/1.92  thf('76', plain,
% 1.73/1.92      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.73/1.92      inference('sup+', [status(thm)], ['62', '67'])).
% 1.73/1.92  thf('77', plain,
% 1.73/1.92      ((m1_subset_1 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 1.73/1.92        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('demod', [status(thm)], ['75', '76'])).
% 1.73/1.92  thf(redefinition_k9_subset_1, axiom,
% 1.73/1.92    (![A:$i,B:$i,C:$i]:
% 1.73/1.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.73/1.92       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.73/1.92  thf('78', plain,
% 1.73/1.92      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.73/1.92         (((k9_subset_1 @ X23 @ X21 @ X22) = (k3_xboole_0 @ X21 @ X22))
% 1.73/1.92          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 1.73/1.92      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.73/1.92  thf('79', plain,
% 1.73/1.92      (![X27 : $i, X28 : $i]:
% 1.73/1.92         ((k1_setfam_1 @ (k2_tarski @ X27 @ X28)) = (k3_xboole_0 @ X27 @ X28))),
% 1.73/1.92      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.73/1.92  thf('80', plain,
% 1.73/1.92      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.73/1.92         (((k9_subset_1 @ X23 @ X21 @ X22)
% 1.73/1.92            = (k1_setfam_1 @ (k2_tarski @ X21 @ X22)))
% 1.73/1.92          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23)))),
% 1.73/1.92      inference('demod', [status(thm)], ['78', '79'])).
% 1.73/1.92  thf('81', plain,
% 1.73/1.92      (![X0 : $i]:
% 1.73/1.92         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.73/1.92           (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.73/1.92           = (k1_setfam_1 @ 
% 1.73/1.92              (k2_tarski @ X0 @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.73/1.92      inference('sup-', [status(thm)], ['77', '80'])).
% 1.73/1.92  thf('82', plain,
% 1.73/1.92      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92         = (k1_setfam_1 @ 
% 1.73/1.92            (k2_tarski @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92             (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.73/1.92      inference('demod', [status(thm)], ['70', '81'])).
% 1.73/1.92  thf('83', plain,
% 1.73/1.92      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.73/1.92      inference('sup+', [status(thm)], ['20', '25'])).
% 1.73/1.92  thf('84', plain,
% 1.73/1.92      (![X8 : $i, X9 : $i]:
% 1.73/1.92         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 1.73/1.92           = (k1_setfam_1 @ (k2_tarski @ X8 @ X9)))),
% 1.73/1.92      inference('demod', [status(thm)], ['44', '45'])).
% 1.73/1.92  thf('85', plain,
% 1.73/1.92      (![X8 : $i, X9 : $i]:
% 1.73/1.92         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 1.73/1.92           = (k1_setfam_1 @ (k2_tarski @ X8 @ X9)))),
% 1.73/1.92      inference('demod', [status(thm)], ['44', '45'])).
% 1.73/1.92  thf('86', plain,
% 1.73/1.92      (![X0 : $i, X1 : $i]:
% 1.73/1.92         ((k4_xboole_0 @ X1 @ (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 1.73/1.92           = (k1_setfam_1 @ (k2_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.73/1.92      inference('sup+', [status(thm)], ['84', '85'])).
% 1.73/1.92  thf('87', plain,
% 1.73/1.92      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92         (k1_setfam_1 @ (k2_tarski @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.73/1.92         = (k1_setfam_1 @ 
% 1.73/1.92            (k2_tarski @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92             (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.73/1.92      inference('sup+', [status(thm)], ['83', '86'])).
% 1.73/1.92  thf('88', plain,
% 1.73/1.92      (![X10 : $i, X11 : $i]:
% 1.73/1.92         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 1.73/1.92      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.73/1.92  thf('89', plain,
% 1.73/1.92      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92         (k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))))
% 1.73/1.92         = (k1_setfam_1 @ 
% 1.73/1.92            (k2_tarski @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92             (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.73/1.92      inference('demod', [status(thm)], ['87', '88'])).
% 1.73/1.92  thf('90', plain,
% 1.73/1.92      (((k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_struct_0 @ sk_A)))
% 1.73/1.92         = (k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))))),
% 1.73/1.92      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 1.73/1.92  thf('91', plain,
% 1.73/1.92      (((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_struct_0 @ sk_A))))),
% 1.73/1.92      inference('clc', [status(thm)], ['60', '61'])).
% 1.73/1.92  thf('92', plain,
% 1.73/1.92      (((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_A))))),
% 1.73/1.92      inference('demod', [status(thm)], ['90', '91'])).
% 1.73/1.92  thf('93', plain,
% 1.73/1.92      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.73/1.92      inference('sup+', [status(thm)], ['62', '67'])).
% 1.73/1.92  thf('94', plain,
% 1.73/1.92      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92         = (k1_setfam_1 @ 
% 1.73/1.92            (k2_tarski @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92             (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.73/1.92      inference('demod', [status(thm)], ['89', '92', '93'])).
% 1.73/1.92  thf('95', plain,
% 1.73/1.92      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.73/1.92      inference('sup+', [status(thm)], ['20', '25'])).
% 1.73/1.92  thf('96', plain,
% 1.73/1.92      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.73/1.92      inference('sup+', [status(thm)], ['62', '67'])).
% 1.73/1.92  thf('97', plain,
% 1.73/1.92      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.73/1.92      inference('demod', [status(thm)], ['95', '96'])).
% 1.73/1.92  thf('98', plain,
% 1.73/1.92      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92         = (k1_setfam_1 @ 
% 1.73/1.92            (k2_tarski @ (u1_struct_0 @ sk_A) @ 
% 1.73/1.92             (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.73/1.92      inference('demod', [status(thm)], ['94', '97'])).
% 1.73/1.92  thf('99', plain,
% 1.73/1.92      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.73/1.92      inference('sup+', [status(thm)], ['82', '98'])).
% 1.73/1.92  thf('100', plain,
% 1.73/1.92      ((((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.73/1.92        | ~ (l1_struct_0 @ sk_A))),
% 1.73/1.92      inference('sup+', [status(thm)], ['2', '99'])).
% 1.73/1.92  thf('101', plain, ((l1_struct_0 @ sk_A)),
% 1.73/1.92      inference('sup-', [status(thm)], ['15', '16'])).
% 1.73/1.92  thf('102', plain,
% 1.73/1.92      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.73/1.92      inference('demod', [status(thm)], ['100', '101'])).
% 1.73/1.92  thf('103', plain,
% 1.73/1.92      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.73/1.92        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('104', plain,
% 1.73/1.92      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.73/1.92      inference('split', [status(esa)], ['103'])).
% 1.73/1.92  thf('105', plain,
% 1.73/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf(d6_pre_topc, axiom,
% 1.73/1.92    (![A:$i]:
% 1.73/1.92     ( ( l1_pre_topc @ A ) =>
% 1.73/1.92       ( ![B:$i]:
% 1.73/1.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.73/1.92           ( ( v4_pre_topc @ B @ A ) <=>
% 1.73/1.92             ( v3_pre_topc @
% 1.73/1.92               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ 
% 1.73/1.92               A ) ) ) ) ))).
% 1.73/1.92  thf('106', plain,
% 1.73/1.92      (![X30 : $i, X31 : $i]:
% 1.73/1.92         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.73/1.92          | ~ (v4_pre_topc @ X30 @ X31)
% 1.73/1.92          | (v3_pre_topc @ 
% 1.73/1.92             (k7_subset_1 @ (u1_struct_0 @ X31) @ (k2_struct_0 @ X31) @ X30) @ 
% 1.73/1.92             X31)
% 1.73/1.92          | ~ (l1_pre_topc @ X31))),
% 1.73/1.92      inference('cnf', [status(esa)], [d6_pre_topc])).
% 1.73/1.92  thf('107', plain,
% 1.73/1.92      ((~ (l1_pre_topc @ sk_A)
% 1.73/1.92        | (v3_pre_topc @ 
% 1.73/1.92           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 1.73/1.92           sk_A)
% 1.73/1.92        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.73/1.92      inference('sup-', [status(thm)], ['105', '106'])).
% 1.73/1.92  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('109', plain,
% 1.73/1.92      (((v3_pre_topc @ 
% 1.73/1.92         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 1.73/1.92         sk_A)
% 1.73/1.92        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.73/1.92      inference('demod', [status(thm)], ['107', '108'])).
% 1.73/1.92  thf('110', plain,
% 1.73/1.92      (((v3_pre_topc @ 
% 1.73/1.92         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 1.73/1.92         sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['104', '109'])).
% 1.73/1.92  thf('111', plain,
% 1.73/1.92      (((v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 1.73/1.92         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.73/1.92      inference('sup+', [status(thm)], ['102', '110'])).
% 1.73/1.92  thf('112', plain,
% 1.73/1.92      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.73/1.92      inference('sup+', [status(thm)], ['62', '67'])).
% 1.73/1.92  thf('113', plain,
% 1.73/1.92      (![X29 : $i]:
% 1.73/1.92         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.73/1.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.73/1.92  thf('114', plain,
% 1.73/1.92      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.73/1.92      inference('sup-', [status(thm)], ['9', '10'])).
% 1.73/1.92  thf('115', plain,
% 1.73/1.92      ((~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 1.73/1.92         <= (~
% 1.73/1.92             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 1.73/1.92      inference('split', [status(esa)], ['0'])).
% 1.73/1.92  thf('116', plain,
% 1.73/1.92      ((~ (v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 1.73/1.92         <= (~
% 1.73/1.92             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['114', '115'])).
% 1.73/1.92  thf('117', plain,
% 1.73/1.92      (((~ (v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.73/1.92         | ~ (l1_struct_0 @ sk_A)))
% 1.73/1.92         <= (~
% 1.73/1.92             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['113', '116'])).
% 1.73/1.92  thf('118', plain, ((l1_struct_0 @ sk_A)),
% 1.73/1.92      inference('sup-', [status(thm)], ['15', '16'])).
% 1.73/1.92  thf('119', plain,
% 1.73/1.92      ((~ (v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 1.73/1.92         <= (~
% 1.73/1.92             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 1.73/1.92      inference('demod', [status(thm)], ['117', '118'])).
% 1.73/1.92  thf('120', plain,
% 1.73/1.92      ((~ (v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 1.73/1.92         <= (~
% 1.73/1.92             ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['112', '119'])).
% 1.73/1.92  thf('121', plain,
% 1.73/1.92      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 1.73/1.92       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.73/1.92      inference('sup-', [status(thm)], ['111', '120'])).
% 1.73/1.92  thf('122', plain,
% 1.73/1.92      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 1.73/1.92       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.73/1.92      inference('split', [status(esa)], ['103'])).
% 1.73/1.92  thf('123', plain,
% 1.73/1.92      (((k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92         = (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.73/1.92      inference('sup+', [status(thm)], ['62', '67'])).
% 1.73/1.92  thf('124', plain,
% 1.73/1.92      (![X29 : $i]:
% 1.73/1.92         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 1.73/1.92      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.73/1.92  thf('125', plain,
% 1.73/1.92      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.73/1.92      inference('sup-', [status(thm)], ['9', '10'])).
% 1.73/1.92  thf('126', plain,
% 1.73/1.92      (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 1.73/1.92         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 1.73/1.92      inference('split', [status(esa)], ['103'])).
% 1.73/1.92  thf('127', plain,
% 1.73/1.92      (((v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 1.73/1.92         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 1.73/1.92      inference('sup+', [status(thm)], ['125', '126'])).
% 1.73/1.92  thf('128', plain,
% 1.73/1.92      ((((v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.73/1.92         | ~ (l1_struct_0 @ sk_A)))
% 1.73/1.92         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 1.73/1.92      inference('sup+', [status(thm)], ['124', '127'])).
% 1.73/1.92  thf('129', plain, ((l1_struct_0 @ sk_A)),
% 1.73/1.92      inference('sup-', [status(thm)], ['15', '16'])).
% 1.73/1.92  thf('130', plain,
% 1.73/1.92      (((v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 1.73/1.92         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 1.73/1.92      inference('demod', [status(thm)], ['128', '129'])).
% 1.73/1.92  thf('131', plain,
% 1.73/1.92      (((v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 1.73/1.92         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 1.73/1.92      inference('sup+', [status(thm)], ['123', '130'])).
% 1.73/1.92  thf('132', plain,
% 1.73/1.92      (((k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.73/1.92         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.73/1.92      inference('demod', [status(thm)], ['100', '101'])).
% 1.73/1.92  thf('133', plain,
% 1.73/1.92      (![X30 : $i, X31 : $i]:
% 1.73/1.92         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.73/1.92          | ~ (v3_pre_topc @ 
% 1.73/1.92               (k7_subset_1 @ (u1_struct_0 @ X31) @ (k2_struct_0 @ X31) @ X30) @ 
% 1.73/1.92               X31)
% 1.73/1.92          | (v4_pre_topc @ X30 @ X31)
% 1.73/1.92          | ~ (l1_pre_topc @ X31))),
% 1.73/1.92      inference('cnf', [status(esa)], [d6_pre_topc])).
% 1.73/1.92  thf('134', plain,
% 1.73/1.92      ((~ (v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.73/1.92        | ~ (l1_pre_topc @ sk_A)
% 1.73/1.92        | (v4_pre_topc @ sk_B @ sk_A)
% 1.73/1.92        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.73/1.92      inference('sup-', [status(thm)], ['132', '133'])).
% 1.73/1.92  thf('135', plain, ((l1_pre_topc @ sk_A)),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('136', plain,
% 1.73/1.92      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.73/1.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.92  thf('137', plain,
% 1.73/1.92      ((~ (v3_pre_topc @ (k5_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.73/1.92        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.73/1.92      inference('demod', [status(thm)], ['134', '135', '136'])).
% 1.73/1.92  thf('138', plain,
% 1.73/1.92      (((v4_pre_topc @ sk_B @ sk_A))
% 1.73/1.92         <= (((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)))),
% 1.73/1.92      inference('sup-', [status(thm)], ['131', '137'])).
% 1.73/1.92  thf('139', plain,
% 1.73/1.92      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.73/1.92      inference('split', [status(esa)], ['0'])).
% 1.73/1.92  thf('140', plain,
% 1.73/1.92      (~ ((v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)) | 
% 1.73/1.92       ((v4_pre_topc @ sk_B @ sk_A))),
% 1.73/1.92      inference('sup-', [status(thm)], ['138', '139'])).
% 1.73/1.92  thf('141', plain, ($false),
% 1.73/1.92      inference('sat_resolution*', [status(thm)], ['1', '121', '122', '140'])).
% 1.73/1.92  
% 1.73/1.92  % SZS output end Refutation
% 1.73/1.92  
% 1.73/1.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
