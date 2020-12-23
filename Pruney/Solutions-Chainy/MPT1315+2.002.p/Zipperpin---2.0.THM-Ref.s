%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oFTOFvqysP

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 233 expanded)
%              Number of leaves         :   31 (  82 expanded)
%              Depth                    :   15
%              Number of atoms          :  768 (2755 expanded)
%              Number of equality atoms :   47 ( 164 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t34_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v4_pre_topc @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                   => ( ( D = B )
                     => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_pre_topc @ C @ A )
               => ( ( v4_pre_topc @ B @ A )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                     => ( ( D = B )
                       => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_tops_2])).

thf('0',plain,(
    ~ ( v4_pre_topc @ sk_D_2 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_D_2 = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ~ ( v4_pre_topc @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_D_2 = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

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
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

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
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ X0 @ sk_B )
      = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_B ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf(t43_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( ( v4_pre_topc @ C @ B )
              <=> ? [D: $i] :
                    ( ( ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) )
                      = C )
                    & ( v4_pre_topc @ D @ A )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X27 ) @ X30 @ ( k2_struct_0 @ X27 ) )
       != X29 )
      | ~ ( v4_pre_topc @ X30 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v4_pre_topc @ X29 @ X27 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t43_pre_topc])).

thf('16',plain,(
    ! [X27: $i,X28: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X27 ) @ X30 @ ( k2_struct_0 @ X27 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X27 ) @ X30 @ ( k2_struct_0 @ X27 ) ) @ X27 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v4_pre_topc @ X30 @ X28 )
      | ~ ( m1_pre_topc @ X27 @ X28 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k1_setfam_1 @ ( k2_tarski @ ( k2_struct_0 @ sk_C_1 ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( v4_pre_topc @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_C_1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('19',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
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
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('21',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('22',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_B ) ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['22'])).

thf('31',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('32',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('33',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k1_setfam_1 @ ( k2_tarski @ X5 @ X6 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference(eq_fact,[status(thm)],['22'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_B
      = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_C_1 ) @ sk_B ) ) )
    | ( sk_B
      = ( k1_setfam_1 @ ( k2_tarski @ ( u1_struct_0 @ sk_C_1 ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','37'])).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('41',plain,
    ( ( sk_B
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_C_1 ) ) ) )
    | ( sk_B
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( sk_B
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( sk_B
      = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ) ) )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['19','42'])).

thf('44',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('45',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( l1_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['46','47'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('49',plain,(
    ! [X24: $i] :
      ( ( l1_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('50',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( sk_B
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['43','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_B ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('54',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('55',plain,
    ( sk_B
    = ( k1_setfam_1 @ ( k2_tarski @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['43','50'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( v4_pre_topc @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v4_pre_topc @ sk_B @ sk_C_1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18','51','52','53','54','55'])).

thf('57',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_C_1 )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v4_pre_topc @ sk_B @ sk_C_1 ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['2','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oFTOFvqysP
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:39:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 230 iterations in 0.078s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.54  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.54  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.54  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.54  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.21/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.54  thf(t34_tops_2, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.54               ( ( v4_pre_topc @ B @ A ) =>
% 0.21/0.54                 ( ![D:$i]:
% 0.21/0.54                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.21/0.54                     ( ( ( D ) = ( B ) ) => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( l1_pre_topc @ A ) =>
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54              ( ![C:$i]:
% 0.21/0.54                ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.54                  ( ( v4_pre_topc @ B @ A ) =>
% 0.21/0.54                    ( ![D:$i]:
% 0.21/0.54                      ( ( m1_subset_1 @
% 0.21/0.54                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.21/0.54                        ( ( ( D ) = ( B ) ) => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t34_tops_2])).
% 0.21/0.54  thf('0', plain, (~ (v4_pre_topc @ sk_D_2 @ sk_C_1)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('1', plain, (((sk_D_2) = (sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('2', plain, (~ (v4_pre_topc @ sk_B @ sk_C_1)),
% 0.21/0.54      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('5', plain, (((sk_D_2) = (sk_B))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.54  thf(commutativity_k9_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.54         (((k9_subset_1 @ X12 @ X14 @ X13) = (k9_subset_1 @ X12 @ X13 @ X14))
% 0.21/0.54          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.21/0.54      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ X0 @ sk_B)
% 0.21/0.54           = (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.54  thf(redefinition_k9_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.54         (((k9_subset_1 @ X17 @ X15 @ X16) = (k3_xboole_0 @ X15 @ X16))
% 0.21/0.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.21/0.54  thf(t12_setfam_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X18 : $i, X19 : $i]:
% 0.21/0.54         ((k1_setfam_1 @ (k2_tarski @ X18 @ X19)) = (k3_xboole_0 @ X18 @ X19))),
% 0.21/0.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.54         (((k9_subset_1 @ X17 @ X15 @ X16)
% 0.21/0.54            = (k1_setfam_1 @ (k2_tarski @ X15 @ X16)))
% 0.21/0.54          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.21/0.54      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ X0 @ sk_B)
% 0.21/0.54           = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['9', '12'])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k1_setfam_1 @ (k2_tarski @ X0 @ sk_B))
% 0.21/0.54           = (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ X0))),
% 0.21/0.54      inference('demod', [status(thm)], ['8', '13'])).
% 0.21/0.54  thf(t43_pre_topc, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.54               ( ( v4_pre_topc @ C @ B ) <=>
% 0.21/0.54                 ( ?[D:$i]:
% 0.21/0.54                   ( ( ( k9_subset_1 @
% 0.21/0.54                         ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) =
% 0.21/0.54                       ( C ) ) & 
% 0.21/0.54                     ( v4_pre_topc @ D @ A ) & 
% 0.21/0.54                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.54         (~ (m1_pre_topc @ X27 @ X28)
% 0.21/0.54          | ((k9_subset_1 @ (u1_struct_0 @ X27) @ X30 @ (k2_struct_0 @ X27))
% 0.21/0.54              != (X29))
% 0.21/0.54          | ~ (v4_pre_topc @ X30 @ X28)
% 0.21/0.54          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.21/0.54          | (v4_pre_topc @ X29 @ X27)
% 0.21/0.54          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.21/0.54          | ~ (l1_pre_topc @ X28))),
% 0.21/0.54      inference('cnf', [status(esa)], [t43_pre_topc])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (![X27 : $i, X28 : $i, X30 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X28)
% 0.21/0.54          | ~ (m1_subset_1 @ 
% 0.21/0.54               (k9_subset_1 @ (u1_struct_0 @ X27) @ X30 @ (k2_struct_0 @ X27)) @ 
% 0.21/0.54               (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.21/0.54          | (v4_pre_topc @ 
% 0.21/0.54             (k9_subset_1 @ (u1_struct_0 @ X27) @ X30 @ (k2_struct_0 @ X27)) @ 
% 0.21/0.54             X27)
% 0.21/0.54          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.21/0.54          | ~ (v4_pre_topc @ X30 @ X28)
% 0.21/0.54          | ~ (m1_pre_topc @ X27 @ X28))),
% 0.21/0.54      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ 
% 0.21/0.54             (k1_setfam_1 @ (k2_tarski @ (k2_struct_0 @ sk_C_1) @ sk_B)) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.54          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.21/0.54          | ~ (v4_pre_topc @ sk_B @ X0)
% 0.21/0.54          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.54          | (v4_pre_topc @ 
% 0.21/0.54             (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ 
% 0.21/0.54              (k2_struct_0 @ sk_C_1)) @ 
% 0.21/0.54             sk_C_1)
% 0.21/0.54          | ~ (l1_pre_topc @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['14', '16'])).
% 0.21/0.54  thf(commutativity_k2_tarski, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      (![X10 : $i, X11 : $i]:
% 0.21/0.54         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 0.21/0.54      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.54  thf(d3_struct_0, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (![X23 : $i]:
% 0.21/0.54         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.54  thf(d4_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.21/0.54       ( ![D:$i]:
% 0.21/0.54         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.54           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.21/0.54         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 0.21/0.54          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.21/0.54          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.21/0.54      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      (![X18 : $i, X19 : $i]:
% 0.21/0.54         ((k1_setfam_1 @ (k2_tarski @ X18 @ X19)) = (k3_xboole_0 @ X18 @ X19))),
% 0.21/0.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.21/0.54         (((X9) = (k1_setfam_1 @ (k2_tarski @ X5 @ X6)))
% 0.21/0.54          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.21/0.54          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.21/0.54      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.21/0.54          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.21/0.54      inference('eq_fact', [status(thm)], ['22'])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.54      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.55  thf(t3_subset, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      (![X20 : $i, X21 : $i]:
% 0.21/0.55         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.55  thf('26', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.55  thf(d3_tarski, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.55          | (r2_hidden @ X0 @ X2)
% 0.21/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.21/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (((sk_B) = (k1_setfam_1 @ (k2_tarski @ X0 @ sk_B)))
% 0.21/0.55          | (r2_hidden @ (sk_D @ sk_B @ sk_B @ X0) @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['23', '28'])).
% 0.21/0.55  thf('30', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.21/0.55          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.21/0.55      inference('eq_fact', [status(thm)], ['22'])).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.21/0.55         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 0.21/0.55          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.21/0.55          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.21/0.55          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.21/0.55      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (![X18 : $i, X19 : $i]:
% 0.21/0.55         ((k1_setfam_1 @ (k2_tarski @ X18 @ X19)) = (k3_xboole_0 @ X18 @ X19))),
% 0.21/0.55      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i, X9 : $i]:
% 0.21/0.55         (((X9) = (k1_setfam_1 @ (k2_tarski @ X5 @ X6)))
% 0.21/0.55          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 0.21/0.55          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 0.21/0.55          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 0.21/0.55      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.21/0.55          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.21/0.55          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.21/0.55          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['30', '33'])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.21/0.55          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.21/0.55          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.21/0.55      inference('simplify', [status(thm)], ['34'])).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.21/0.55          | ((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0))))),
% 0.21/0.55      inference('eq_fact', [status(thm)], ['22'])).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (((X0) = (k1_setfam_1 @ (k2_tarski @ X1 @ X0)))
% 0.21/0.55          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.21/0.55      inference('clc', [status(thm)], ['35', '36'])).
% 0.21/0.55  thf('38', plain,
% 0.21/0.55      ((((sk_B) = (k1_setfam_1 @ (k2_tarski @ (u1_struct_0 @ sk_C_1) @ sk_B)))
% 0.21/0.55        | ((sk_B) = (k1_setfam_1 @ (k2_tarski @ (u1_struct_0 @ sk_C_1) @ sk_B))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['29', '37'])).
% 0.21/0.55  thf('39', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i]:
% 0.21/0.55         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 0.21/0.55      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.55  thf('40', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i]:
% 0.21/0.55         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 0.21/0.55      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.55  thf('41', plain,
% 0.21/0.55      ((((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_C_1))))
% 0.21/0.55        | ((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_C_1)))))),
% 0.21/0.55      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.21/0.55  thf('42', plain,
% 0.21/0.55      (((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (u1_struct_0 @ sk_C_1))))),
% 0.21/0.55      inference('simplify', [status(thm)], ['41'])).
% 0.21/0.55  thf('43', plain,
% 0.21/0.55      ((((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_struct_0 @ sk_C_1))))
% 0.21/0.55        | ~ (l1_struct_0 @ sk_C_1))),
% 0.21/0.55      inference('sup+', [status(thm)], ['19', '42'])).
% 0.21/0.55  thf('44', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(dt_m1_pre_topc, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_pre_topc @ A ) =>
% 0.21/0.55       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.55  thf('45', plain,
% 0.21/0.55      (![X25 : $i, X26 : $i]:
% 0.21/0.55         (~ (m1_pre_topc @ X25 @ X26)
% 0.21/0.55          | (l1_pre_topc @ X25)
% 0.21/0.55          | ~ (l1_pre_topc @ X26))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.55  thf('46', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.55  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('48', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.55      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.55  thf(dt_l1_pre_topc, axiom,
% 0.21/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.55  thf('49', plain,
% 0.21/0.55      (![X24 : $i]: ((l1_struct_0 @ X24) | ~ (l1_pre_topc @ X24))),
% 0.21/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.55  thf('50', plain, ((l1_struct_0 @ sk_C_1)),
% 0.21/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.55  thf('51', plain,
% 0.21/0.55      (((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_struct_0 @ sk_C_1))))),
% 0.21/0.55      inference('demod', [status(thm)], ['43', '50'])).
% 0.21/0.55  thf('52', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.55  thf('53', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k1_setfam_1 @ (k2_tarski @ X0 @ sk_B))
% 0.21/0.55           = (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ X0))),
% 0.21/0.55      inference('demod', [status(thm)], ['8', '13'])).
% 0.21/0.55  thf('54', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i]:
% 0.21/0.55         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 0.21/0.55      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.55  thf('55', plain,
% 0.21/0.55      (((sk_B) = (k1_setfam_1 @ (k2_tarski @ sk_B @ (k2_struct_0 @ sk_C_1))))),
% 0.21/0.55      inference('demod', [status(thm)], ['43', '50'])).
% 0.21/0.55  thf('56', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.21/0.55          | ~ (v4_pre_topc @ sk_B @ X0)
% 0.21/0.55          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.55          | (v4_pre_topc @ sk_B @ sk_C_1)
% 0.21/0.55          | ~ (l1_pre_topc @ X0))),
% 0.21/0.55      inference('demod', [status(thm)],
% 0.21/0.55                ['17', '18', '51', '52', '53', '54', '55'])).
% 0.21/0.55  thf('57', plain,
% 0.21/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | (v4_pre_topc @ sk_B @ sk_C_1)
% 0.21/0.55        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.21/0.55        | ~ (m1_pre_topc @ sk_C_1 @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['3', '56'])).
% 0.21/0.55  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('59', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('60', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('61', plain, ((v4_pre_topc @ sk_B @ sk_C_1)),
% 0.21/0.55      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.21/0.55  thf('62', plain, ($false), inference('demod', [status(thm)], ['2', '61'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
