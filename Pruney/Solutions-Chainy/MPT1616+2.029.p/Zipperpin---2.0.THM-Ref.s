%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gIfBsbKlOY

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:23 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 260 expanded)
%              Number of leaves         :   50 ( 103 expanded)
%              Depth                    :   28
%              Number of atoms          :  911 (2096 expanded)
%              Number of equality atoms :   25 (  59 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X49: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X49 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(redefinition_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k5_setfam_1 @ A @ B )
        = ( k3_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k5_setfam_1 @ X12 @ X11 )
        = ( k3_tarski @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) )
                      & ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) )
                   => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )
          & ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
               => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) )
          & ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_5 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
       => ( zip_tseitin_4 @ B @ A ) ) ) )).

thf(zf_stmt_2,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_4 @ B @ A )
    <=> ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
       => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_3 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ! [C: $i] :
            ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
    <=> ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ( zip_tseitin_1 @ C @ B @ A ) ) ) )).

thf(zf_stmt_8,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_9,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ C @ B @ A )
       => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_10,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_11,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
    <=> ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
        & ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_12,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
          & ! [B: $i] :
              ( zip_tseitin_5 @ B @ A )
          & ! [B: $i] :
              ( zip_tseitin_3 @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X46: $i] :
      ( ~ ( v2_pre_topc @ X46 )
      | ( r2_hidden @ ( u1_struct_0 @ X46 ) @ ( u1_pre_topc @ X46 ) )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( m1_subset_1 @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('9',plain,(
    ! [X4: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X4: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X4: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ( m1_subset_1 @ X7 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['22'])).

thf('24',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('26',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(condensation,[status(thm)],['31'])).

thf(t56_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B )
        & ( r2_hidden @ C @ A ) )
     => ( r1_tarski @ C @ B ) ) )).

thf('33',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ X16 ) @ X17 )
      | ~ ( r2_hidden @ X18 @ X16 )
      | ( r1_tarski @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t56_setfam_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k3_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','34'])).

thf(d12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_setfam_1 @ B @ A )
    <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('36',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_setfam_1 @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ ( k3_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_setfam_1 @ ( u1_pre_topc @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X49: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X49 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t60_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( m1_setfam_1 @ B @ A )
      <=> ( ( k5_setfam_1 @ A @ B )
          = A ) ) ) )).

thf('39',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_setfam_1 @ X23 @ X22 )
      | ( ( k5_setfam_1 @ X22 @ X23 )
        = X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t60_setfam_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( m1_setfam_1 @ ( u1_pre_topc @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('46',plain,(
    ! [X46: $i,X48: $i] :
      ( ~ ( v2_pre_topc @ X46 )
      | ( zip_tseitin_5 @ X48 @ X46 )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('47',plain,(
    ! [X49: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X49 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) ) )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('48',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) ) )
      | ( zip_tseitin_4 @ X43 @ X44 )
      | ~ ( zip_tseitin_5 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( zip_tseitin_5 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(condensation,[status(thm)],['31'])).

thf('53',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r1_tarski @ X40 @ ( u1_pre_topc @ X41 ) )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X41 ) @ X40 ) @ ( u1_pre_topc @ X41 ) )
      | ~ ( zip_tseitin_4 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('58',plain,(
    ! [X50: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X50 ) @ X50 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X50 ) )
        = ( k3_tarski @ X50 ) )
      | ( v1_xboole_0 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_pre_topc @ X0 ) )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(t24_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) )
        = ( u1_struct_0 @ A ) ) ) )).

thf(zf_stmt_13,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) )
          = ( u1_struct_0 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_yellow_1])).

thf('60',plain,(
    ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('61',plain,
    ( ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
     != ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('64',plain,
    ( ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
     != ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('68',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    v1_xboole_0 @ ( u1_pre_topc @ sk_A ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X46: $i] :
      ( ~ ( v2_pre_topc @ X46 )
      | ( r2_hidden @ ( u1_struct_0 @ X46 ) @ ( u1_pre_topc @ X46 ) )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['73','74','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gIfBsbKlOY
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:29:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.84  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.84  % Solved by: fo/fo7.sh
% 0.58/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.84  % done 856 iterations in 0.391s
% 0.58/0.84  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.84  % SZS output start Refutation
% 0.58/0.84  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.58/0.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.84  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.58/0.84  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.58/0.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.84  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.58/0.84  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.58/0.84  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.58/0.84  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.84  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.58/0.84  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.84  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.58/0.84  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.58/0.84  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.58/0.84  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.58/0.84  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.58/0.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.84  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.58/0.84  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.58/0.84  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.58/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.84  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.58/0.84  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 0.58/0.84  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.58/0.84  thf(dt_u1_pre_topc, axiom,
% 0.58/0.84    (![A:$i]:
% 0.58/0.84     ( ( l1_pre_topc @ A ) =>
% 0.58/0.84       ( m1_subset_1 @
% 0.58/0.84         ( u1_pre_topc @ A ) @ 
% 0.58/0.84         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.58/0.84  thf('0', plain,
% 0.58/0.84      (![X49 : $i]:
% 0.58/0.84         ((m1_subset_1 @ (u1_pre_topc @ X49) @ 
% 0.58/0.84           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49))))
% 0.58/0.84          | ~ (l1_pre_topc @ X49))),
% 0.58/0.84      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.58/0.84  thf(redefinition_k5_setfam_1, axiom,
% 0.58/0.84    (![A:$i,B:$i]:
% 0.58/0.84     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.58/0.84       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 0.58/0.84  thf('1', plain,
% 0.58/0.84      (![X11 : $i, X12 : $i]:
% 0.58/0.84         (((k5_setfam_1 @ X12 @ X11) = (k3_tarski @ X11))
% 0.58/0.84          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.58/0.84      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 0.58/0.84  thf('2', plain,
% 0.58/0.84      (![X0 : $i]:
% 0.58/0.84         (~ (l1_pre_topc @ X0)
% 0.58/0.84          | ((k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.58/0.84              = (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.58/0.84      inference('sup-', [status(thm)], ['0', '1'])).
% 0.58/0.84  thf(d1_pre_topc, axiom,
% 0.58/0.84    (![A:$i]:
% 0.58/0.84     ( ( l1_pre_topc @ A ) =>
% 0.58/0.84       ( ( v2_pre_topc @ A ) <=>
% 0.58/0.84         ( ( ![B:$i]:
% 0.58/0.84             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.84               ( ![C:$i]:
% 0.58/0.84                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.84                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.58/0.84                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.58/0.84                     ( r2_hidden @
% 0.58/0.84                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.58/0.84                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.58/0.84           ( ![B:$i]:
% 0.58/0.84             ( ( m1_subset_1 @
% 0.58/0.84                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.58/0.84               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.58/0.84                 ( r2_hidden @
% 0.58/0.84                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.58/0.84                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.58/0.84           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.58/0.84  thf(zf_stmt_0, type, zip_tseitin_5 : $i > $i > $o).
% 0.58/0.84  thf(zf_stmt_1, axiom,
% 0.58/0.84    (![B:$i,A:$i]:
% 0.58/0.84     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.58/0.84       ( ( m1_subset_1 @
% 0.58/0.84           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.58/0.84         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.58/0.84  thf(zf_stmt_2, type, zip_tseitin_4 : $i > $i > $o).
% 0.58/0.84  thf(zf_stmt_3, axiom,
% 0.58/0.84    (![B:$i,A:$i]:
% 0.58/0.84     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.58/0.84       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.58/0.84         ( r2_hidden @
% 0.58/0.84           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.58/0.84  thf(zf_stmt_4, type, zip_tseitin_3 : $i > $i > $o).
% 0.58/0.84  thf(zf_stmt_5, axiom,
% 0.58/0.84    (![B:$i,A:$i]:
% 0.58/0.84     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.58/0.84       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.84         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.58/0.84  thf(zf_stmt_6, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.58/0.84  thf(zf_stmt_7, axiom,
% 0.58/0.84    (![C:$i,B:$i,A:$i]:
% 0.58/0.84     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.58/0.84       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.84         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.58/0.84  thf(zf_stmt_8, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.58/0.84  thf(zf_stmt_9, axiom,
% 0.58/0.84    (![C:$i,B:$i,A:$i]:
% 0.58/0.84     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.58/0.84       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.58/0.84         ( r2_hidden @
% 0.58/0.84           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.58/0.84  thf(zf_stmt_10, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.58/0.84  thf(zf_stmt_11, axiom,
% 0.58/0.84    (![C:$i,B:$i,A:$i]:
% 0.58/0.84     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.58/0.84       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.58/0.84         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.58/0.84  thf(zf_stmt_12, axiom,
% 0.58/0.84    (![A:$i]:
% 0.58/0.84     ( ( l1_pre_topc @ A ) =>
% 0.58/0.84       ( ( v2_pre_topc @ A ) <=>
% 0.58/0.84         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.58/0.84           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.58/0.84           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.58/0.84  thf('3', plain,
% 0.58/0.84      (![X46 : $i]:
% 0.58/0.84         (~ (v2_pre_topc @ X46)
% 0.58/0.84          | (r2_hidden @ (u1_struct_0 @ X46) @ (u1_pre_topc @ X46))
% 0.58/0.84          | ~ (l1_pre_topc @ X46))),
% 0.58/0.84      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.58/0.84  thf(t94_zfmisc_1, axiom,
% 0.58/0.84    (![A:$i,B:$i]:
% 0.58/0.84     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 0.58/0.84       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 0.58/0.84  thf('4', plain,
% 0.58/0.84      (![X0 : $i, X1 : $i]:
% 0.58/0.84         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 0.58/0.84          | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.58/0.84      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.58/0.84  thf(d2_subset_1, axiom,
% 0.58/0.84    (![A:$i,B:$i]:
% 0.58/0.84     ( ( ( v1_xboole_0 @ A ) =>
% 0.58/0.85         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.58/0.85       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.58/0.85         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.58/0.85  thf('5', plain,
% 0.58/0.85      (![X5 : $i, X6 : $i]:
% 0.58/0.85         (~ (r2_hidden @ X5 @ X6)
% 0.58/0.85          | (m1_subset_1 @ X5 @ X6)
% 0.58/0.85          | (v1_xboole_0 @ X6))),
% 0.58/0.85      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.58/0.85  thf('6', plain,
% 0.58/0.85      (![X0 : $i, X1 : $i]:
% 0.58/0.85         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 0.58/0.85          | (v1_xboole_0 @ X0)
% 0.58/0.85          | (m1_subset_1 @ (sk_C @ X1 @ X0) @ X0))),
% 0.58/0.85      inference('sup-', [status(thm)], ['4', '5'])).
% 0.58/0.85  thf(t3_subset, axiom,
% 0.58/0.85    (![A:$i,B:$i]:
% 0.58/0.85     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.58/0.85  thf('7', plain,
% 0.58/0.85      (![X13 : $i, X14 : $i]:
% 0.58/0.85         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.58/0.85      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.85  thf('8', plain,
% 0.58/0.85      (![X0 : $i, X1 : $i]:
% 0.58/0.85         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.58/0.85          | (r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X1)
% 0.58/0.85          | (r1_tarski @ (sk_C @ X1 @ (k1_zfmisc_1 @ X0)) @ X0))),
% 0.58/0.85      inference('sup-', [status(thm)], ['6', '7'])).
% 0.58/0.85  thf(t99_zfmisc_1, axiom,
% 0.58/0.85    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.58/0.85  thf('9', plain, (![X4 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X4)) = (X4))),
% 0.58/0.85      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.58/0.85  thf('10', plain,
% 0.58/0.85      (![X0 : $i, X1 : $i]:
% 0.58/0.85         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.58/0.85          | (r1_tarski @ X0 @ X1)
% 0.58/0.85          | (r1_tarski @ (sk_C @ X1 @ (k1_zfmisc_1 @ X0)) @ X0))),
% 0.58/0.85      inference('demod', [status(thm)], ['8', '9'])).
% 0.58/0.85  thf('11', plain,
% 0.58/0.85      (![X0 : $i, X1 : $i]:
% 0.58/0.85         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 0.58/0.85          | ~ (r1_tarski @ (sk_C @ X1 @ X0) @ X1))),
% 0.58/0.85      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.58/0.85  thf('12', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         ((r1_tarski @ X0 @ X0)
% 0.58/0.85          | (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.58/0.85          | (r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X0))),
% 0.58/0.85      inference('sup-', [status(thm)], ['10', '11'])).
% 0.58/0.85  thf('13', plain, (![X4 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X4)) = (X4))),
% 0.58/0.85      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.58/0.85  thf('14', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         ((r1_tarski @ X0 @ X0)
% 0.58/0.85          | (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.58/0.85          | (r1_tarski @ X0 @ X0))),
% 0.58/0.85      inference('demod', [status(thm)], ['12', '13'])).
% 0.58/0.85  thf('15', plain,
% 0.58/0.85      (![X0 : $i]: ((v1_xboole_0 @ (k1_zfmisc_1 @ X0)) | (r1_tarski @ X0 @ X0))),
% 0.58/0.85      inference('simplify', [status(thm)], ['14'])).
% 0.58/0.85  thf('16', plain, (![X4 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X4)) = (X4))),
% 0.58/0.85      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.58/0.85  thf('17', plain,
% 0.58/0.85      (![X0 : $i, X1 : $i]:
% 0.58/0.85         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 0.58/0.85          | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.58/0.85      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.58/0.85  thf('18', plain,
% 0.58/0.85      (![X0 : $i]: ((v1_xboole_0 @ (k1_zfmisc_1 @ X0)) | (r1_tarski @ X0 @ X0))),
% 0.58/0.85      inference('simplify', [status(thm)], ['14'])).
% 0.58/0.85  thf('19', plain,
% 0.58/0.85      (![X6 : $i, X7 : $i]:
% 0.58/0.85         (~ (v1_xboole_0 @ X7) | (m1_subset_1 @ X7 @ X6) | ~ (v1_xboole_0 @ X6))),
% 0.58/0.85      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.58/0.85  thf('20', plain,
% 0.58/0.85      (![X13 : $i, X14 : $i]:
% 0.58/0.85         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.58/0.85      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.85  thf('21', plain,
% 0.58/0.85      (![X0 : $i, X1 : $i]:
% 0.58/0.85         (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.58/0.85          | ~ (v1_xboole_0 @ X1)
% 0.58/0.85          | (r1_tarski @ X1 @ X0))),
% 0.58/0.85      inference('sup-', [status(thm)], ['19', '20'])).
% 0.58/0.85  thf('22', plain,
% 0.58/0.85      (![X0 : $i, X1 : $i]:
% 0.58/0.85         ((r1_tarski @ X0 @ X0) | (r1_tarski @ X1 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.58/0.85      inference('sup-', [status(thm)], ['18', '21'])).
% 0.58/0.85  thf('23', plain,
% 0.58/0.85      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.58/0.85      inference('eq_fact', [status(thm)], ['22'])).
% 0.58/0.85  thf('24', plain,
% 0.58/0.85      (![X13 : $i, X15 : $i]:
% 0.58/0.85         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 0.58/0.85      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.85  thf('25', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         (~ (v1_xboole_0 @ X0) | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.58/0.85      inference('sup-', [status(thm)], ['23', '24'])).
% 0.58/0.85  thf(t5_subset, axiom,
% 0.58/0.85    (![A:$i,B:$i,C:$i]:
% 0.58/0.85     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.58/0.85          ( v1_xboole_0 @ C ) ) ))).
% 0.58/0.85  thf('26', plain,
% 0.58/0.85      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.58/0.85         (~ (r2_hidden @ X19 @ X20)
% 0.58/0.85          | ~ (v1_xboole_0 @ X21)
% 0.58/0.85          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.58/0.85      inference('cnf', [status(esa)], [t5_subset])).
% 0.58/0.85  thf('27', plain,
% 0.58/0.85      (![X0 : $i, X1 : $i]:
% 0.58/0.85         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.58/0.85      inference('sup-', [status(thm)], ['25', '26'])).
% 0.58/0.85  thf('28', plain,
% 0.58/0.85      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.58/0.85      inference('simplify', [status(thm)], ['27'])).
% 0.58/0.85  thf('29', plain,
% 0.58/0.85      (![X0 : $i, X1 : $i]:
% 0.58/0.85         ((r1_tarski @ (k3_tarski @ X0) @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.58/0.85      inference('sup-', [status(thm)], ['17', '28'])).
% 0.58/0.85  thf('30', plain,
% 0.58/0.85      (![X0 : $i, X1 : $i]:
% 0.58/0.85         ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 0.58/0.85      inference('sup+', [status(thm)], ['16', '29'])).
% 0.58/0.85  thf('31', plain,
% 0.58/0.85      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X1))),
% 0.58/0.85      inference('sup-', [status(thm)], ['15', '30'])).
% 0.58/0.85  thf('32', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.58/0.85      inference('condensation', [status(thm)], ['31'])).
% 0.58/0.85  thf(t56_setfam_1, axiom,
% 0.58/0.85    (![A:$i,B:$i,C:$i]:
% 0.58/0.85     ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B ) & ( r2_hidden @ C @ A ) ) =>
% 0.58/0.85       ( r1_tarski @ C @ B ) ))).
% 0.58/0.85  thf('33', plain,
% 0.58/0.85      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.58/0.85         (~ (r1_tarski @ (k3_tarski @ X16) @ X17)
% 0.58/0.85          | ~ (r2_hidden @ X18 @ X16)
% 0.58/0.85          | (r1_tarski @ X18 @ X17))),
% 0.58/0.85      inference('cnf', [status(esa)], [t56_setfam_1])).
% 0.58/0.85  thf('34', plain,
% 0.58/0.85      (![X0 : $i, X1 : $i]:
% 0.58/0.85         ((r1_tarski @ X1 @ (k3_tarski @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.58/0.85      inference('sup-', [status(thm)], ['32', '33'])).
% 0.58/0.85  thf('35', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         (~ (l1_pre_topc @ X0)
% 0.58/0.85          | ~ (v2_pre_topc @ X0)
% 0.58/0.85          | (r1_tarski @ (u1_struct_0 @ X0) @ (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.58/0.85      inference('sup-', [status(thm)], ['3', '34'])).
% 0.58/0.85  thf(d12_setfam_1, axiom,
% 0.58/0.85    (![A:$i,B:$i]:
% 0.58/0.85     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.58/0.85  thf('36', plain,
% 0.58/0.85      (![X8 : $i, X10 : $i]:
% 0.58/0.85         ((m1_setfam_1 @ X10 @ X8) | ~ (r1_tarski @ X8 @ (k3_tarski @ X10)))),
% 0.58/0.85      inference('cnf', [status(esa)], [d12_setfam_1])).
% 0.58/0.85  thf('37', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         (~ (v2_pre_topc @ X0)
% 0.58/0.85          | ~ (l1_pre_topc @ X0)
% 0.58/0.85          | (m1_setfam_1 @ (u1_pre_topc @ X0) @ (u1_struct_0 @ X0)))),
% 0.58/0.85      inference('sup-', [status(thm)], ['35', '36'])).
% 0.58/0.85  thf('38', plain,
% 0.58/0.85      (![X49 : $i]:
% 0.58/0.85         ((m1_subset_1 @ (u1_pre_topc @ X49) @ 
% 0.58/0.85           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49))))
% 0.58/0.85          | ~ (l1_pre_topc @ X49))),
% 0.58/0.85      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.58/0.85  thf(t60_setfam_1, axiom,
% 0.58/0.85    (![A:$i,B:$i]:
% 0.58/0.85     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.58/0.85       ( ( m1_setfam_1 @ B @ A ) <=> ( ( k5_setfam_1 @ A @ B ) = ( A ) ) ) ))).
% 0.58/0.85  thf('39', plain,
% 0.58/0.85      (![X22 : $i, X23 : $i]:
% 0.58/0.85         (~ (m1_setfam_1 @ X23 @ X22)
% 0.58/0.85          | ((k5_setfam_1 @ X22 @ X23) = (X22))
% 0.58/0.85          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 0.58/0.85      inference('cnf', [status(esa)], [t60_setfam_1])).
% 0.58/0.85  thf('40', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         (~ (l1_pre_topc @ X0)
% 0.58/0.85          | ((k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.58/0.85              = (u1_struct_0 @ X0))
% 0.58/0.85          | ~ (m1_setfam_1 @ (u1_pre_topc @ X0) @ (u1_struct_0 @ X0)))),
% 0.58/0.85      inference('sup-', [status(thm)], ['38', '39'])).
% 0.58/0.85  thf('41', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         (~ (l1_pre_topc @ X0)
% 0.58/0.85          | ~ (v2_pre_topc @ X0)
% 0.58/0.85          | ((k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.58/0.85              = (u1_struct_0 @ X0))
% 0.58/0.85          | ~ (l1_pre_topc @ X0))),
% 0.58/0.85      inference('sup-', [status(thm)], ['37', '40'])).
% 0.58/0.85  thf('42', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         (((k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.58/0.85            = (u1_struct_0 @ X0))
% 0.58/0.85          | ~ (v2_pre_topc @ X0)
% 0.58/0.85          | ~ (l1_pre_topc @ X0))),
% 0.58/0.85      inference('simplify', [status(thm)], ['41'])).
% 0.58/0.85  thf('43', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         (((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ X0))
% 0.58/0.85          | ~ (l1_pre_topc @ X0)
% 0.58/0.85          | ~ (l1_pre_topc @ X0)
% 0.58/0.85          | ~ (v2_pre_topc @ X0))),
% 0.58/0.85      inference('sup+', [status(thm)], ['2', '42'])).
% 0.58/0.85  thf('44', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         (~ (v2_pre_topc @ X0)
% 0.58/0.85          | ~ (l1_pre_topc @ X0)
% 0.58/0.85          | ((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ X0)))),
% 0.58/0.85      inference('simplify', [status(thm)], ['43'])).
% 0.58/0.85  thf('45', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         (~ (l1_pre_topc @ X0)
% 0.58/0.85          | ((k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.58/0.85              = (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.58/0.85      inference('sup-', [status(thm)], ['0', '1'])).
% 0.58/0.85  thf('46', plain,
% 0.58/0.85      (![X46 : $i, X48 : $i]:
% 0.58/0.85         (~ (v2_pre_topc @ X46)
% 0.58/0.85          | (zip_tseitin_5 @ X48 @ X46)
% 0.58/0.85          | ~ (l1_pre_topc @ X46))),
% 0.58/0.85      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.58/0.85  thf('47', plain,
% 0.58/0.85      (![X49 : $i]:
% 0.58/0.85         ((m1_subset_1 @ (u1_pre_topc @ X49) @ 
% 0.58/0.85           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49))))
% 0.58/0.85          | ~ (l1_pre_topc @ X49))),
% 0.58/0.85      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.58/0.85  thf('48', plain,
% 0.58/0.85      (![X43 : $i, X44 : $i]:
% 0.58/0.85         (~ (m1_subset_1 @ X43 @ 
% 0.58/0.85             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44))))
% 0.58/0.85          | (zip_tseitin_4 @ X43 @ X44)
% 0.58/0.85          | ~ (zip_tseitin_5 @ X43 @ X44))),
% 0.58/0.85      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.58/0.85  thf('49', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         (~ (l1_pre_topc @ X0)
% 0.58/0.85          | ~ (zip_tseitin_5 @ (u1_pre_topc @ X0) @ X0)
% 0.58/0.85          | (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0))),
% 0.58/0.85      inference('sup-', [status(thm)], ['47', '48'])).
% 0.58/0.85  thf('50', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         (~ (l1_pre_topc @ X0)
% 0.58/0.85          | ~ (v2_pre_topc @ X0)
% 0.58/0.85          | (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0)
% 0.58/0.85          | ~ (l1_pre_topc @ X0))),
% 0.58/0.85      inference('sup-', [status(thm)], ['46', '49'])).
% 0.58/0.85  thf('51', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         ((zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0)
% 0.58/0.85          | ~ (v2_pre_topc @ X0)
% 0.58/0.85          | ~ (l1_pre_topc @ X0))),
% 0.58/0.85      inference('simplify', [status(thm)], ['50'])).
% 0.58/0.85  thf('52', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.58/0.85      inference('condensation', [status(thm)], ['31'])).
% 0.58/0.85  thf('53', plain,
% 0.58/0.85      (![X40 : $i, X41 : $i]:
% 0.58/0.85         (~ (r1_tarski @ X40 @ (u1_pre_topc @ X41))
% 0.58/0.85          | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ X41) @ X40) @ 
% 0.58/0.85             (u1_pre_topc @ X41))
% 0.58/0.85          | ~ (zip_tseitin_4 @ X40 @ X41))),
% 0.58/0.85      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.58/0.85  thf('54', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         (~ (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0)
% 0.58/0.85          | (r2_hidden @ 
% 0.58/0.85             (k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 0.58/0.85             (u1_pre_topc @ X0)))),
% 0.58/0.85      inference('sup-', [status(thm)], ['52', '53'])).
% 0.58/0.85  thf('55', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         (~ (l1_pre_topc @ X0)
% 0.58/0.85          | ~ (v2_pre_topc @ X0)
% 0.58/0.85          | (r2_hidden @ 
% 0.58/0.85             (k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 0.58/0.85             (u1_pre_topc @ X0)))),
% 0.58/0.85      inference('sup-', [status(thm)], ['51', '54'])).
% 0.58/0.85  thf('56', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         ((r2_hidden @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_pre_topc @ X0))
% 0.58/0.85          | ~ (l1_pre_topc @ X0)
% 0.58/0.85          | ~ (v2_pre_topc @ X0)
% 0.58/0.85          | ~ (l1_pre_topc @ X0))),
% 0.58/0.85      inference('sup+', [status(thm)], ['45', '55'])).
% 0.58/0.85  thf('57', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         (~ (v2_pre_topc @ X0)
% 0.58/0.85          | ~ (l1_pre_topc @ X0)
% 0.58/0.85          | (r2_hidden @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_pre_topc @ X0)))),
% 0.58/0.85      inference('simplify', [status(thm)], ['56'])).
% 0.58/0.85  thf(t14_yellow_1, axiom,
% 0.58/0.85    (![A:$i]:
% 0.58/0.85     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.58/0.85       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.58/0.85         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.58/0.85  thf('58', plain,
% 0.58/0.85      (![X50 : $i]:
% 0.58/0.85         (~ (r2_hidden @ (k3_tarski @ X50) @ X50)
% 0.58/0.85          | ((k4_yellow_0 @ (k2_yellow_1 @ X50)) = (k3_tarski @ X50))
% 0.58/0.85          | (v1_xboole_0 @ X50))),
% 0.58/0.85      inference('cnf', [status(esa)], [t14_yellow_1])).
% 0.58/0.85  thf('59', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         (~ (l1_pre_topc @ X0)
% 0.58/0.85          | ~ (v2_pre_topc @ X0)
% 0.58/0.85          | (v1_xboole_0 @ (u1_pre_topc @ X0))
% 0.58/0.85          | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 0.58/0.85              = (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.58/0.85      inference('sup-', [status(thm)], ['57', '58'])).
% 0.58/0.85  thf(t24_yellow_1, conjecture,
% 0.58/0.85    (![A:$i]:
% 0.58/0.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.85       ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.58/0.85         ( u1_struct_0 @ A ) ) ))).
% 0.58/0.85  thf(zf_stmt_13, negated_conjecture,
% 0.58/0.85    (~( ![A:$i]:
% 0.58/0.85        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.58/0.85            ( l1_pre_topc @ A ) ) =>
% 0.58/0.85          ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.58/0.85            ( u1_struct_0 @ A ) ) ) )),
% 0.58/0.85    inference('cnf.neg', [status(esa)], [t24_yellow_1])).
% 0.58/0.85  thf('60', plain,
% 0.58/0.85      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 0.58/0.85         != (u1_struct_0 @ sk_A))),
% 0.58/0.85      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.58/0.85  thf('61', plain,
% 0.58/0.85      ((((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))
% 0.58/0.85        | (v1_xboole_0 @ (u1_pre_topc @ sk_A))
% 0.58/0.85        | ~ (v2_pre_topc @ sk_A)
% 0.58/0.85        | ~ (l1_pre_topc @ sk_A))),
% 0.58/0.85      inference('sup-', [status(thm)], ['59', '60'])).
% 0.58/0.85  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.85      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.58/0.85  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.85      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.58/0.85  thf('64', plain,
% 0.58/0.85      ((((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))
% 0.58/0.85        | (v1_xboole_0 @ (u1_pre_topc @ sk_A)))),
% 0.58/0.85      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.58/0.85  thf('65', plain,
% 0.58/0.85      ((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.58/0.85        | ~ (l1_pre_topc @ sk_A)
% 0.58/0.85        | ~ (v2_pre_topc @ sk_A)
% 0.58/0.85        | (v1_xboole_0 @ (u1_pre_topc @ sk_A)))),
% 0.58/0.85      inference('sup-', [status(thm)], ['44', '64'])).
% 0.58/0.85  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.85      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.58/0.85  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.85      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.58/0.85  thf('68', plain,
% 0.58/0.85      ((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.58/0.85        | (v1_xboole_0 @ (u1_pre_topc @ sk_A)))),
% 0.58/0.85      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.58/0.85  thf('69', plain, ((v1_xboole_0 @ (u1_pre_topc @ sk_A))),
% 0.58/0.85      inference('simplify', [status(thm)], ['68'])).
% 0.58/0.85  thf('70', plain,
% 0.58/0.85      (![X46 : $i]:
% 0.58/0.85         (~ (v2_pre_topc @ X46)
% 0.58/0.85          | (r2_hidden @ (u1_struct_0 @ X46) @ (u1_pre_topc @ X46))
% 0.58/0.85          | ~ (l1_pre_topc @ X46))),
% 0.58/0.85      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.58/0.85  thf('71', plain,
% 0.58/0.85      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.58/0.85      inference('simplify', [status(thm)], ['27'])).
% 0.58/0.85  thf('72', plain,
% 0.58/0.85      (![X0 : $i]:
% 0.58/0.85         (~ (l1_pre_topc @ X0)
% 0.58/0.85          | ~ (v2_pre_topc @ X0)
% 0.58/0.85          | ~ (v1_xboole_0 @ (u1_pre_topc @ X0)))),
% 0.58/0.85      inference('sup-', [status(thm)], ['70', '71'])).
% 0.58/0.85  thf('73', plain, ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.58/0.85      inference('sup-', [status(thm)], ['69', '72'])).
% 0.58/0.85  thf('74', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.85      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.58/0.85  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.85      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.58/0.85  thf('76', plain, ($false),
% 0.58/0.85      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.58/0.85  
% 0.58/0.85  % SZS output end Refutation
% 0.58/0.85  
% 0.58/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
