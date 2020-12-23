%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tcHL2PuePN

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:07 EST 2020

% Result     : Theorem 2.05s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 148 expanded)
%              Number of leaves         :   32 (  58 expanded)
%              Depth                    :   13
%              Number of atoms          :  795 (1969 expanded)
%              Number of equality atoms :   56 ( 107 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( v3_pre_topc @ X29 @ X30 )
      | ( ( k2_pre_topc @ X30 @ ( k9_subset_1 @ ( u1_struct_0 @ X30 ) @ X29 @ ( k2_pre_topc @ X30 @ X31 ) ) )
        = ( k2_pre_topc @ X30 @ ( k9_subset_1 @ ( u1_struct_0 @ X30 ) @ X29 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X12 @ X14 @ X13 )
        = ( k9_subset_1 @ X12 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k9_subset_1 @ X20 @ X18 @ X19 )
        = ( k3_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('19',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ ( k2_pre_topc @ sk_A @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['3','4','5','12','17','18','19'])).

thf('21',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','20'])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v1_tops_1 @ X27 @ X28 )
      | ( ( k2_pre_topc @ X28 @ X27 )
        = ( k2_struct_0 @ X28 ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ ( k2_struct_0 @ sk_A ) ) )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['21','27'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('29',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('30',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k4_xboole_0 @ sk_C @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_C @ X0 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['30'])).

thf('37',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['30'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('43',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( sk_C
        = ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['35','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( sk_C
      = ( k4_xboole_0 @ sk_C @ ( k4_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('47',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_C
      = ( k3_xboole_0 @ sk_C @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['29','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('51',plain,(
    ! [X26: $i] :
      ( ( l1_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('52',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','53'])).

thf('55',plain,(
    ( k2_pre_topc @ sk_A @ sk_C )
 != ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k9_subset_1 @ X20 @ X18 @ X19 )
        = ( k3_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('60',plain,(
    ( k2_pre_topc @ sk_A @ sk_C )
 != ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['55','58','59'])).

thf('61',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tcHL2PuePN
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:32:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.05/2.26  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.05/2.26  % Solved by: fo/fo7.sh
% 2.05/2.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.05/2.26  % done 2080 iterations in 1.805s
% 2.05/2.26  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.05/2.26  % SZS output start Refutation
% 2.05/2.26  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.05/2.26  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 2.05/2.26  thf(sk_A_type, type, sk_A: $i).
% 2.05/2.26  thf(sk_B_type, type, sk_B: $i).
% 2.05/2.26  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.05/2.26  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 2.05/2.26  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 2.05/2.26  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.05/2.26  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 2.05/2.26  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.05/2.26  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.05/2.26  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.05/2.26  thf(sk_C_type, type, sk_C: $i).
% 2.05/2.26  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.05/2.26  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 2.05/2.26  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.05/2.26  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.05/2.26  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.05/2.26  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.05/2.26  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 2.05/2.26  thf(t81_tops_1, conjecture,
% 2.05/2.26    (![A:$i]:
% 2.05/2.26     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.05/2.26       ( ![B:$i]:
% 2.05/2.26         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.05/2.26           ( ( v1_tops_1 @ B @ A ) =>
% 2.05/2.26             ( ![C:$i]:
% 2.05/2.26               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.05/2.26                 ( ( v3_pre_topc @ C @ A ) =>
% 2.05/2.26                   ( ( k2_pre_topc @ A @ C ) =
% 2.05/2.26                     ( k2_pre_topc @
% 2.05/2.26                       A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ))).
% 2.05/2.26  thf(zf_stmt_0, negated_conjecture,
% 2.05/2.26    (~( ![A:$i]:
% 2.05/2.26        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.05/2.26          ( ![B:$i]:
% 2.05/2.26            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.05/2.26              ( ( v1_tops_1 @ B @ A ) =>
% 2.05/2.26                ( ![C:$i]:
% 2.05/2.26                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.05/2.26                    ( ( v3_pre_topc @ C @ A ) =>
% 2.05/2.26                      ( ( k2_pre_topc @ A @ C ) =
% 2.05/2.26                        ( k2_pre_topc @
% 2.05/2.26                          A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ) )),
% 2.05/2.26    inference('cnf.neg', [status(esa)], [t81_tops_1])).
% 2.05/2.26  thf('0', plain,
% 2.05/2.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.05/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.26  thf('1', plain,
% 2.05/2.26      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.05/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.26  thf(t41_tops_1, axiom,
% 2.05/2.26    (![A:$i]:
% 2.05/2.26     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.05/2.26       ( ![B:$i]:
% 2.05/2.26         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.05/2.26           ( ![C:$i]:
% 2.05/2.26             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.05/2.26               ( ( v3_pre_topc @ B @ A ) =>
% 2.05/2.26                 ( ( k2_pre_topc @
% 2.05/2.26                     A @ 
% 2.05/2.26                     ( k9_subset_1 @
% 2.05/2.26                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) ) =
% 2.05/2.26                   ( k2_pre_topc @
% 2.05/2.26                     A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) ))).
% 2.05/2.26  thf('2', plain,
% 2.05/2.26      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.05/2.26         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 2.05/2.26          | ~ (v3_pre_topc @ X29 @ X30)
% 2.05/2.26          | ((k2_pre_topc @ X30 @ 
% 2.05/2.26              (k9_subset_1 @ (u1_struct_0 @ X30) @ X29 @ 
% 2.05/2.26               (k2_pre_topc @ X30 @ X31)))
% 2.05/2.26              = (k2_pre_topc @ X30 @ 
% 2.05/2.26                 (k9_subset_1 @ (u1_struct_0 @ X30) @ X29 @ X31)))
% 2.05/2.26          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 2.05/2.26          | ~ (l1_pre_topc @ X30)
% 2.05/2.26          | ~ (v2_pre_topc @ X30))),
% 2.05/2.26      inference('cnf', [status(esa)], [t41_tops_1])).
% 2.05/2.26  thf('3', plain,
% 2.05/2.26      (![X0 : $i]:
% 2.05/2.26         (~ (v2_pre_topc @ sk_A)
% 2.05/2.26          | ~ (l1_pre_topc @ sk_A)
% 2.05/2.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.05/2.26          | ((k2_pre_topc @ sk_A @ 
% 2.05/2.26              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.05/2.26               (k2_pre_topc @ sk_A @ X0)))
% 2.05/2.26              = (k2_pre_topc @ sk_A @ 
% 2.05/2.26                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)))
% 2.05/2.26          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 2.05/2.26      inference('sup-', [status(thm)], ['1', '2'])).
% 2.05/2.26  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 2.05/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.26  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 2.05/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.26  thf('6', plain,
% 2.05/2.26      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.05/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.26  thf(commutativity_k9_subset_1, axiom,
% 2.05/2.26    (![A:$i,B:$i,C:$i]:
% 2.05/2.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.05/2.26       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 2.05/2.26  thf('7', plain,
% 2.05/2.26      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.05/2.26         (((k9_subset_1 @ X12 @ X14 @ X13) = (k9_subset_1 @ X12 @ X13 @ X14))
% 2.05/2.26          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 2.05/2.26      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 2.05/2.26  thf('8', plain,
% 2.05/2.26      (![X0 : $i]:
% 2.05/2.26         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 2.05/2.26           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 2.05/2.26      inference('sup-', [status(thm)], ['6', '7'])).
% 2.05/2.26  thf('9', plain,
% 2.05/2.26      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.05/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.26  thf(redefinition_k9_subset_1, axiom,
% 2.05/2.26    (![A:$i,B:$i,C:$i]:
% 2.05/2.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.05/2.26       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 2.05/2.26  thf('10', plain,
% 2.05/2.26      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.05/2.26         (((k9_subset_1 @ X20 @ X18 @ X19) = (k3_xboole_0 @ X18 @ X19))
% 2.05/2.26          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 2.05/2.26      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 2.05/2.26  thf('11', plain,
% 2.05/2.26      (![X0 : $i]:
% 2.05/2.26         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 2.05/2.26           = (k3_xboole_0 @ X0 @ sk_C))),
% 2.05/2.26      inference('sup-', [status(thm)], ['9', '10'])).
% 2.05/2.26  thf('12', plain,
% 2.05/2.26      (![X0 : $i]:
% 2.05/2.26         ((k3_xboole_0 @ X0 @ sk_C)
% 2.05/2.26           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 2.05/2.26      inference('demod', [status(thm)], ['8', '11'])).
% 2.05/2.26  thf(commutativity_k2_tarski, axiom,
% 2.05/2.26    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 2.05/2.26  thf('13', plain,
% 2.05/2.26      (![X10 : $i, X11 : $i]:
% 2.05/2.26         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 2.05/2.26      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 2.05/2.26  thf(t12_setfam_1, axiom,
% 2.05/2.26    (![A:$i,B:$i]:
% 2.05/2.26     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.05/2.26  thf('14', plain,
% 2.05/2.26      (![X21 : $i, X22 : $i]:
% 2.05/2.26         ((k1_setfam_1 @ (k2_tarski @ X21 @ X22)) = (k3_xboole_0 @ X21 @ X22))),
% 2.05/2.26      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.05/2.26  thf('15', plain,
% 2.05/2.26      (![X0 : $i, X1 : $i]:
% 2.05/2.26         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 2.05/2.26      inference('sup+', [status(thm)], ['13', '14'])).
% 2.05/2.26  thf('16', plain,
% 2.05/2.26      (![X21 : $i, X22 : $i]:
% 2.05/2.26         ((k1_setfam_1 @ (k2_tarski @ X21 @ X22)) = (k3_xboole_0 @ X21 @ X22))),
% 2.05/2.26      inference('cnf', [status(esa)], [t12_setfam_1])).
% 2.05/2.26  thf('17', plain,
% 2.05/2.26      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.05/2.26      inference('sup+', [status(thm)], ['15', '16'])).
% 2.05/2.26  thf('18', plain,
% 2.05/2.26      (![X0 : $i]:
% 2.05/2.26         ((k3_xboole_0 @ X0 @ sk_C)
% 2.05/2.26           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 2.05/2.26      inference('demod', [status(thm)], ['8', '11'])).
% 2.05/2.26  thf('19', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 2.05/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.26  thf('20', plain,
% 2.05/2.26      (![X0 : $i]:
% 2.05/2.26         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.05/2.26          | ((k2_pre_topc @ sk_A @ 
% 2.05/2.26              (k3_xboole_0 @ sk_C @ (k2_pre_topc @ sk_A @ X0)))
% 2.05/2.26              = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C))))),
% 2.05/2.26      inference('demod', [status(thm)], ['3', '4', '5', '12', '17', '18', '19'])).
% 2.05/2.26  thf('21', plain,
% 2.05/2.26      (((k2_pre_topc @ sk_A @ 
% 2.05/2.26         (k3_xboole_0 @ sk_C @ (k2_pre_topc @ sk_A @ sk_B)))
% 2.05/2.26         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 2.05/2.26      inference('sup-', [status(thm)], ['0', '20'])).
% 2.05/2.26  thf('22', plain,
% 2.05/2.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.05/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.26  thf(d3_tops_1, axiom,
% 2.05/2.26    (![A:$i]:
% 2.05/2.26     ( ( l1_pre_topc @ A ) =>
% 2.05/2.26       ( ![B:$i]:
% 2.05/2.26         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.05/2.26           ( ( v1_tops_1 @ B @ A ) <=>
% 2.05/2.26             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 2.05/2.26  thf('23', plain,
% 2.05/2.26      (![X27 : $i, X28 : $i]:
% 2.05/2.26         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 2.05/2.26          | ~ (v1_tops_1 @ X27 @ X28)
% 2.05/2.26          | ((k2_pre_topc @ X28 @ X27) = (k2_struct_0 @ X28))
% 2.05/2.26          | ~ (l1_pre_topc @ X28))),
% 2.05/2.26      inference('cnf', [status(esa)], [d3_tops_1])).
% 2.05/2.26  thf('24', plain,
% 2.05/2.26      ((~ (l1_pre_topc @ sk_A)
% 2.05/2.26        | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 2.05/2.26        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 2.05/2.26      inference('sup-', [status(thm)], ['22', '23'])).
% 2.05/2.26  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 2.05/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.26  thf('26', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 2.05/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.26  thf('27', plain, (((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))),
% 2.05/2.26      inference('demod', [status(thm)], ['24', '25', '26'])).
% 2.05/2.26  thf('28', plain,
% 2.05/2.26      (((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ (k2_struct_0 @ sk_A)))
% 2.05/2.26         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 2.05/2.26      inference('demod', [status(thm)], ['21', '27'])).
% 2.05/2.26  thf(d3_struct_0, axiom,
% 2.05/2.26    (![A:$i]:
% 2.05/2.26     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 2.05/2.26  thf('29', plain,
% 2.05/2.26      (![X25 : $i]:
% 2.05/2.26         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 2.05/2.26      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.05/2.26  thf(d5_xboole_0, axiom,
% 2.05/2.26    (![A:$i,B:$i,C:$i]:
% 2.05/2.26     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 2.05/2.26       ( ![D:$i]:
% 2.05/2.26         ( ( r2_hidden @ D @ C ) <=>
% 2.05/2.26           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 2.05/2.26  thf('30', plain,
% 2.05/2.26      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.05/2.26         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 2.05/2.26          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 2.05/2.26          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.05/2.26      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.05/2.26  thf('31', plain,
% 2.05/2.26      (![X0 : $i, X1 : $i]:
% 2.05/2.26         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 2.05/2.26          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 2.05/2.26      inference('eq_fact', [status(thm)], ['30'])).
% 2.05/2.26  thf('32', plain,
% 2.05/2.26      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.05/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.26  thf(l3_subset_1, axiom,
% 2.05/2.26    (![A:$i,B:$i]:
% 2.05/2.26     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.05/2.26       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 2.05/2.26  thf('33', plain,
% 2.05/2.26      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.05/2.26         (~ (r2_hidden @ X15 @ X16)
% 2.05/2.26          | (r2_hidden @ X15 @ X17)
% 2.05/2.26          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 2.05/2.26      inference('cnf', [status(esa)], [l3_subset_1])).
% 2.05/2.26  thf('34', plain,
% 2.05/2.26      (![X0 : $i]:
% 2.05/2.26         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C))),
% 2.05/2.26      inference('sup-', [status(thm)], ['32', '33'])).
% 2.05/2.26  thf('35', plain,
% 2.05/2.26      (![X0 : $i]:
% 2.05/2.26         (((sk_C) = (k4_xboole_0 @ sk_C @ X0))
% 2.05/2.26          | (r2_hidden @ (sk_D @ sk_C @ X0 @ sk_C) @ (u1_struct_0 @ sk_A)))),
% 2.05/2.26      inference('sup-', [status(thm)], ['31', '34'])).
% 2.05/2.26  thf('36', plain,
% 2.05/2.26      (![X0 : $i, X1 : $i]:
% 2.05/2.26         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 2.05/2.26          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 2.05/2.26      inference('eq_fact', [status(thm)], ['30'])).
% 2.05/2.26  thf('37', plain,
% 2.05/2.26      (![X1 : $i, X2 : $i, X5 : $i]:
% 2.05/2.26         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 2.05/2.26          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 2.05/2.26          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 2.05/2.26          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 2.05/2.26      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.05/2.26  thf('38', plain,
% 2.05/2.26      (![X0 : $i, X1 : $i]:
% 2.05/2.26         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 2.05/2.26          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 2.05/2.26          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 2.05/2.26          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 2.05/2.26      inference('sup-', [status(thm)], ['36', '37'])).
% 2.05/2.26  thf('39', plain,
% 2.05/2.26      (![X0 : $i, X1 : $i]:
% 2.05/2.26         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 2.05/2.26          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 2.05/2.26          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 2.05/2.26      inference('simplify', [status(thm)], ['38'])).
% 2.05/2.26  thf('40', plain,
% 2.05/2.26      (![X0 : $i, X1 : $i]:
% 2.05/2.26         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 2.05/2.26          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 2.05/2.26      inference('eq_fact', [status(thm)], ['30'])).
% 2.05/2.26  thf('41', plain,
% 2.05/2.26      (![X0 : $i, X1 : $i]:
% 2.05/2.26         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 2.05/2.26          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 2.05/2.26      inference('clc', [status(thm)], ['39', '40'])).
% 2.05/2.26  thf('42', plain,
% 2.05/2.26      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 2.05/2.26         (~ (r2_hidden @ X4 @ X3)
% 2.05/2.26          | ~ (r2_hidden @ X4 @ X2)
% 2.05/2.26          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 2.05/2.26      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.05/2.26  thf('43', plain,
% 2.05/2.26      (![X1 : $i, X2 : $i, X4 : $i]:
% 2.05/2.26         (~ (r2_hidden @ X4 @ X2)
% 2.05/2.26          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 2.05/2.26      inference('simplify', [status(thm)], ['42'])).
% 2.05/2.26  thf('44', plain,
% 2.05/2.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.05/2.26         (((X2) = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 2.05/2.26          | ~ (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 2.05/2.26      inference('sup-', [status(thm)], ['41', '43'])).
% 2.05/2.26  thf('45', plain,
% 2.05/2.26      (![X0 : $i]:
% 2.05/2.26         (((sk_C)
% 2.05/2.26            = (k4_xboole_0 @ sk_C @ (k4_xboole_0 @ X0 @ (u1_struct_0 @ sk_A))))
% 2.05/2.26          | ((sk_C)
% 2.05/2.26              = (k4_xboole_0 @ sk_C @ (k4_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))))),
% 2.05/2.26      inference('sup-', [status(thm)], ['35', '44'])).
% 2.05/2.26  thf('46', plain,
% 2.05/2.26      (![X0 : $i]:
% 2.05/2.26         ((sk_C)
% 2.05/2.26           = (k4_xboole_0 @ sk_C @ (k4_xboole_0 @ X0 @ (u1_struct_0 @ sk_A))))),
% 2.05/2.26      inference('simplify', [status(thm)], ['45'])).
% 2.05/2.26  thf(t48_xboole_1, axiom,
% 2.05/2.26    (![A:$i,B:$i]:
% 2.05/2.26     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.05/2.26  thf('47', plain,
% 2.05/2.26      (![X8 : $i, X9 : $i]:
% 2.05/2.26         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 2.05/2.26           = (k3_xboole_0 @ X8 @ X9))),
% 2.05/2.26      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.05/2.26  thf('48', plain, (((sk_C) = (k3_xboole_0 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 2.05/2.26      inference('sup+', [status(thm)], ['46', '47'])).
% 2.05/2.26  thf('49', plain,
% 2.05/2.26      ((((sk_C) = (k3_xboole_0 @ sk_C @ (k2_struct_0 @ sk_A)))
% 2.05/2.26        | ~ (l1_struct_0 @ sk_A))),
% 2.05/2.26      inference('sup+', [status(thm)], ['29', '48'])).
% 2.05/2.26  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 2.05/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.26  thf(dt_l1_pre_topc, axiom,
% 2.05/2.26    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 2.05/2.26  thf('51', plain,
% 2.05/2.26      (![X26 : $i]: ((l1_struct_0 @ X26) | ~ (l1_pre_topc @ X26))),
% 2.05/2.26      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 2.05/2.26  thf('52', plain, ((l1_struct_0 @ sk_A)),
% 2.05/2.26      inference('sup-', [status(thm)], ['50', '51'])).
% 2.05/2.26  thf('53', plain, (((sk_C) = (k3_xboole_0 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 2.05/2.26      inference('demod', [status(thm)], ['49', '52'])).
% 2.05/2.26  thf('54', plain,
% 2.05/2.26      (((k2_pre_topc @ sk_A @ sk_C)
% 2.05/2.26         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 2.05/2.26      inference('demod', [status(thm)], ['28', '53'])).
% 2.05/2.26  thf('55', plain,
% 2.05/2.26      (((k2_pre_topc @ sk_A @ sk_C)
% 2.05/2.26         != (k2_pre_topc @ sk_A @ 
% 2.05/2.26             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_B)))),
% 2.05/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.26  thf('56', plain,
% 2.05/2.26      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.05/2.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.26  thf('57', plain,
% 2.05/2.26      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.05/2.26         (((k9_subset_1 @ X20 @ X18 @ X19) = (k3_xboole_0 @ X18 @ X19))
% 2.05/2.26          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 2.05/2.26      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 2.05/2.26  thf('58', plain,
% 2.05/2.26      (![X0 : $i]:
% 2.05/2.26         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 2.05/2.26           = (k3_xboole_0 @ X0 @ sk_B))),
% 2.05/2.26      inference('sup-', [status(thm)], ['56', '57'])).
% 2.05/2.26  thf('59', plain,
% 2.05/2.26      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.05/2.26      inference('sup+', [status(thm)], ['15', '16'])).
% 2.05/2.26  thf('60', plain,
% 2.05/2.26      (((k2_pre_topc @ sk_A @ sk_C)
% 2.05/2.26         != (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 2.05/2.26      inference('demod', [status(thm)], ['55', '58', '59'])).
% 2.05/2.26  thf('61', plain, ($false),
% 2.05/2.26      inference('simplify_reflect-', [status(thm)], ['54', '60'])).
% 2.05/2.26  
% 2.05/2.26  % SZS output end Refutation
% 2.05/2.26  
% 2.05/2.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
