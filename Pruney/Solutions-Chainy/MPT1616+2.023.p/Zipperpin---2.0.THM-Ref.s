%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PRgsus3259

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:22 EST 2020

% Result     : Theorem 0.98s
% Output     : Refutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 215 expanded)
%              Number of leaves         :   47 (  90 expanded)
%              Depth                    :   26
%              Number of atoms          :  797 (1729 expanded)
%              Number of equality atoms :   26 (  55 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

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

thf('0',plain,(
    ! [X40: $i] :
      ( ~ ( v2_pre_topc @ X40 )
      | ( r2_hidden @ ( u1_struct_0 @ X40 ) @ ( u1_pre_topc @ X40 ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ ( k3_tarski @ X4 ) )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X0 @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( m1_subset_1 @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X5 ) @ X6 )
      | ~ ( r1_tarski @ ( sk_C @ X6 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','24'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X43: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X43 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('27',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k3_tarski @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k3_tarski @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['0','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k3_tarski @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X43: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X43 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('33',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t95_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('35',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X7 ) @ ( k3_tarski @ X8 ) )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t95_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( k3_tarski @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X40: $i] :
      ( ~ ( v2_pre_topc @ X40 )
      | ( r2_hidden @ ( u1_struct_0 @ X40 ) @ ( u1_pre_topc @ X40 ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ ( k3_tarski @ X4 ) )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X40: $i] :
      ( ~ ( v2_pre_topc @ X40 )
      | ( r2_hidden @ ( u1_struct_0 @ X40 ) @ ( u1_pre_topc @ X40 ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('48',plain,(
    ! [X44: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X44 ) @ X44 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X44 ) )
        = ( k3_tarski @ X44 ) )
      | ( v1_xboole_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('50',plain,(
    ! [X44: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ X44 ) )
        = ( k3_tarski @ X44 ) )
      | ~ ( r2_hidden @ ( k3_tarski @ X44 ) @ X44 ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

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

thf('54',plain,(
    ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('55',plain,
    ( ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('57',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('58',plain,(
    ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['45','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('62',plain,(
    ( u1_struct_0 @ sk_A )
 != ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    $false ),
    inference(simplify,[status(thm)],['62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PRgsus3259
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:16:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.98/1.21  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.98/1.21  % Solved by: fo/fo7.sh
% 0.98/1.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.98/1.21  % done 950 iterations in 0.757s
% 0.98/1.21  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.98/1.21  % SZS output start Refutation
% 0.98/1.21  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.98/1.21  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.98/1.21  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.98/1.21  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.98/1.21  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.98/1.21  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.98/1.21  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.98/1.21  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.98/1.21  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.98/1.21  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.98/1.21  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.98/1.21  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.98/1.21  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.98/1.21  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.98/1.21  thf(sk_A_type, type, sk_A: $i).
% 0.98/1.21  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.98/1.21  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.98/1.21  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.98/1.21  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.98/1.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.98/1.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.98/1.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.98/1.21  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.98/1.21  thf(d1_pre_topc, axiom,
% 0.98/1.21    (![A:$i]:
% 0.98/1.21     ( ( l1_pre_topc @ A ) =>
% 0.98/1.21       ( ( v2_pre_topc @ A ) <=>
% 0.98/1.21         ( ( ![B:$i]:
% 0.98/1.21             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.98/1.21               ( ![C:$i]:
% 0.98/1.21                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.98/1.21                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.98/1.21                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.98/1.21                     ( r2_hidden @
% 0.98/1.21                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.98/1.21                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.98/1.21           ( ![B:$i]:
% 0.98/1.21             ( ( m1_subset_1 @
% 0.98/1.21                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.98/1.21               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.98/1.21                 ( r2_hidden @
% 0.98/1.21                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.98/1.21                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.98/1.21           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.98/1.21  thf(zf_stmt_0, type, zip_tseitin_5 : $i > $i > $o).
% 0.98/1.21  thf(zf_stmt_1, axiom,
% 0.98/1.21    (![B:$i,A:$i]:
% 0.98/1.21     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.98/1.21       ( ( m1_subset_1 @
% 0.98/1.21           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.98/1.21         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.98/1.21  thf(zf_stmt_2, type, zip_tseitin_4 : $i > $i > $o).
% 0.98/1.21  thf(zf_stmt_3, axiom,
% 0.98/1.21    (![B:$i,A:$i]:
% 0.98/1.21     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.98/1.21       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.98/1.21         ( r2_hidden @
% 0.98/1.21           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.98/1.21  thf(zf_stmt_4, type, zip_tseitin_3 : $i > $i > $o).
% 0.98/1.21  thf(zf_stmt_5, axiom,
% 0.98/1.21    (![B:$i,A:$i]:
% 0.98/1.21     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.98/1.21       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.98/1.21         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.98/1.21  thf(zf_stmt_6, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.98/1.21  thf(zf_stmt_7, axiom,
% 0.98/1.21    (![C:$i,B:$i,A:$i]:
% 0.98/1.21     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.98/1.21       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.98/1.21         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.98/1.21  thf(zf_stmt_8, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.98/1.21  thf(zf_stmt_9, axiom,
% 0.98/1.21    (![C:$i,B:$i,A:$i]:
% 0.98/1.21     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.98/1.21       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.98/1.21         ( r2_hidden @
% 0.98/1.21           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.98/1.21  thf(zf_stmt_10, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.98/1.21  thf(zf_stmt_11, axiom,
% 0.98/1.21    (![C:$i,B:$i,A:$i]:
% 0.98/1.21     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.98/1.21       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.98/1.21         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.98/1.21  thf(zf_stmt_12, axiom,
% 0.98/1.21    (![A:$i]:
% 0.98/1.21     ( ( l1_pre_topc @ A ) =>
% 0.98/1.21       ( ( v2_pre_topc @ A ) <=>
% 0.98/1.21         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.98/1.21           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.98/1.21           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.98/1.21  thf('0', plain,
% 0.98/1.21      (![X40 : $i]:
% 0.98/1.21         (~ (v2_pre_topc @ X40)
% 0.98/1.21          | (r2_hidden @ (u1_struct_0 @ X40) @ (u1_pre_topc @ X40))
% 0.98/1.21          | ~ (l1_pre_topc @ X40))),
% 0.98/1.21      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.98/1.21  thf(d10_xboole_0, axiom,
% 0.98/1.21    (![A:$i,B:$i]:
% 0.98/1.21     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.98/1.21  thf('1', plain,
% 0.98/1.21      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.98/1.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.98/1.21  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.98/1.21      inference('simplify', [status(thm)], ['1'])).
% 0.98/1.21  thf(t3_subset, axiom,
% 0.98/1.21    (![A:$i,B:$i]:
% 0.98/1.21     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.98/1.21  thf('3', plain,
% 0.98/1.21      (![X12 : $i, X14 : $i]:
% 0.98/1.21         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.98/1.21      inference('cnf', [status(esa)], [t3_subset])).
% 0.98/1.21  thf('4', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.98/1.21      inference('sup-', [status(thm)], ['2', '3'])).
% 0.98/1.21  thf(d2_subset_1, axiom,
% 0.98/1.21    (![A:$i,B:$i]:
% 0.98/1.21     ( ( ( v1_xboole_0 @ A ) =>
% 0.98/1.21         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.98/1.21       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.98/1.21         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.98/1.21  thf('5', plain,
% 0.98/1.21      (![X9 : $i, X10 : $i]:
% 0.98/1.21         (~ (m1_subset_1 @ X9 @ X10)
% 0.98/1.21          | (r2_hidden @ X9 @ X10)
% 0.98/1.21          | (v1_xboole_0 @ X10))),
% 0.98/1.21      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.98/1.21  thf('6', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.98/1.21          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.98/1.21      inference('sup-', [status(thm)], ['4', '5'])).
% 0.98/1.21  thf(l49_zfmisc_1, axiom,
% 0.98/1.21    (![A:$i,B:$i]:
% 0.98/1.21     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.98/1.21  thf('7', plain,
% 0.98/1.21      (![X3 : $i, X4 : $i]:
% 0.98/1.21         ((r1_tarski @ X3 @ (k3_tarski @ X4)) | ~ (r2_hidden @ X3 @ X4))),
% 0.98/1.21      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.98/1.21  thf('8', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.98/1.21          | (r1_tarski @ X0 @ (k3_tarski @ (k1_zfmisc_1 @ X0))))),
% 0.98/1.21      inference('sup-', [status(thm)], ['6', '7'])).
% 0.98/1.21  thf(t94_zfmisc_1, axiom,
% 0.98/1.21    (![A:$i,B:$i]:
% 0.98/1.21     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 0.98/1.21       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 0.98/1.21  thf('9', plain,
% 0.98/1.21      (![X5 : $i, X6 : $i]:
% 0.98/1.21         ((r1_tarski @ (k3_tarski @ X5) @ X6)
% 0.98/1.21          | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 0.98/1.21      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.98/1.21  thf('10', plain,
% 0.98/1.21      (![X9 : $i, X10 : $i]:
% 0.98/1.21         (~ (r2_hidden @ X9 @ X10)
% 0.98/1.21          | (m1_subset_1 @ X9 @ X10)
% 0.98/1.21          | (v1_xboole_0 @ X10))),
% 0.98/1.21      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.98/1.21  thf('11', plain,
% 0.98/1.21      (![X0 : $i, X1 : $i]:
% 0.98/1.21         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 0.98/1.21          | (v1_xboole_0 @ X0)
% 0.98/1.21          | (m1_subset_1 @ (sk_C @ X1 @ X0) @ X0))),
% 0.98/1.21      inference('sup-', [status(thm)], ['9', '10'])).
% 0.98/1.21  thf('12', plain,
% 0.98/1.21      (![X5 : $i, X6 : $i]:
% 0.98/1.21         ((r1_tarski @ (k3_tarski @ X5) @ X6)
% 0.98/1.21          | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 0.98/1.21      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.98/1.21  thf('13', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.98/1.21      inference('sup-', [status(thm)], ['2', '3'])).
% 0.98/1.21  thf(t5_subset, axiom,
% 0.98/1.21    (![A:$i,B:$i,C:$i]:
% 0.98/1.21     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.98/1.21          ( v1_xboole_0 @ C ) ) ))).
% 0.98/1.21  thf('14', plain,
% 0.98/1.21      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.98/1.21         (~ (r2_hidden @ X15 @ X16)
% 0.98/1.21          | ~ (v1_xboole_0 @ X17)
% 0.98/1.21          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.98/1.21      inference('cnf', [status(esa)], [t5_subset])).
% 0.98/1.21  thf('15', plain,
% 0.98/1.21      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.98/1.21      inference('sup-', [status(thm)], ['13', '14'])).
% 0.98/1.21  thf('16', plain,
% 0.98/1.21      (![X0 : $i, X1 : $i]:
% 0.98/1.21         ((r1_tarski @ (k3_tarski @ X0) @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.98/1.21      inference('sup-', [status(thm)], ['12', '15'])).
% 0.98/1.21  thf('17', plain,
% 0.98/1.21      (![X0 : $i, X1 : $i]:
% 0.98/1.21         ((m1_subset_1 @ (sk_C @ X1 @ X0) @ X0)
% 0.98/1.21          | (r1_tarski @ (k3_tarski @ X0) @ X1))),
% 0.98/1.21      inference('clc', [status(thm)], ['11', '16'])).
% 0.98/1.21  thf('18', plain,
% 0.98/1.21      (![X12 : $i, X13 : $i]:
% 0.98/1.21         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.98/1.21      inference('cnf', [status(esa)], [t3_subset])).
% 0.98/1.21  thf('19', plain,
% 0.98/1.21      (![X0 : $i, X1 : $i]:
% 0.98/1.21         ((r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X1)
% 0.98/1.21          | (r1_tarski @ (sk_C @ X1 @ (k1_zfmisc_1 @ X0)) @ X0))),
% 0.98/1.21      inference('sup-', [status(thm)], ['17', '18'])).
% 0.98/1.21  thf('20', plain,
% 0.98/1.21      (![X5 : $i, X6 : $i]:
% 0.98/1.21         ((r1_tarski @ (k3_tarski @ X5) @ X6)
% 0.98/1.21          | ~ (r1_tarski @ (sk_C @ X6 @ X5) @ X6))),
% 0.98/1.21      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.98/1.21  thf('21', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         ((r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X0)
% 0.98/1.21          | (r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X0))),
% 0.98/1.21      inference('sup-', [status(thm)], ['19', '20'])).
% 0.98/1.21  thf('22', plain,
% 0.98/1.21      (![X0 : $i]: (r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X0)),
% 0.98/1.21      inference('simplify', [status(thm)], ['21'])).
% 0.98/1.21  thf('23', plain,
% 0.98/1.21      (![X0 : $i, X2 : $i]:
% 0.98/1.21         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.98/1.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.98/1.21  thf('24', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (~ (r1_tarski @ X0 @ (k3_tarski @ (k1_zfmisc_1 @ X0)))
% 0.98/1.21          | ((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0))))),
% 0.98/1.21      inference('sup-', [status(thm)], ['22', '23'])).
% 0.98/1.21  thf('25', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.98/1.21          | ((X0) = (k3_tarski @ (k1_zfmisc_1 @ X0))))),
% 0.98/1.21      inference('sup-', [status(thm)], ['8', '24'])).
% 0.98/1.21  thf(dt_u1_pre_topc, axiom,
% 0.98/1.21    (![A:$i]:
% 0.98/1.21     ( ( l1_pre_topc @ A ) =>
% 0.98/1.21       ( m1_subset_1 @
% 0.98/1.21         ( u1_pre_topc @ A ) @ 
% 0.98/1.21         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.98/1.21  thf('26', plain,
% 0.98/1.21      (![X43 : $i]:
% 0.98/1.21         ((m1_subset_1 @ (u1_pre_topc @ X43) @ 
% 0.98/1.21           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43))))
% 0.98/1.21          | ~ (l1_pre_topc @ X43))),
% 0.98/1.21      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.98/1.21  thf('27', plain,
% 0.98/1.21      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.98/1.21         (~ (r2_hidden @ X15 @ X16)
% 0.98/1.21          | ~ (v1_xboole_0 @ X17)
% 0.98/1.21          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.98/1.21      inference('cnf', [status(esa)], [t5_subset])).
% 0.98/1.21  thf('28', plain,
% 0.98/1.21      (![X0 : $i, X1 : $i]:
% 0.98/1.21         (~ (l1_pre_topc @ X0)
% 0.98/1.21          | ~ (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.98/1.21          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0)))),
% 0.98/1.21      inference('sup-', [status(thm)], ['26', '27'])).
% 0.98/1.21  thf('29', plain,
% 0.98/1.21      (![X0 : $i, X1 : $i]:
% 0.98/1.21         (((u1_struct_0 @ X0)
% 0.98/1.21            = (k3_tarski @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.98/1.21          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0))
% 0.98/1.21          | ~ (l1_pre_topc @ X0))),
% 0.98/1.21      inference('sup-', [status(thm)], ['25', '28'])).
% 0.98/1.21  thf('30', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (~ (l1_pre_topc @ X0)
% 0.98/1.21          | ~ (v2_pre_topc @ X0)
% 0.98/1.21          | ~ (l1_pre_topc @ X0)
% 0.98/1.21          | ((u1_struct_0 @ X0)
% 0.98/1.21              = (k3_tarski @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))),
% 0.98/1.21      inference('sup-', [status(thm)], ['0', '29'])).
% 0.98/1.21  thf('31', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (((u1_struct_0 @ X0)
% 0.98/1.21            = (k3_tarski @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.98/1.21          | ~ (v2_pre_topc @ X0)
% 0.98/1.21          | ~ (l1_pre_topc @ X0))),
% 0.98/1.21      inference('simplify', [status(thm)], ['30'])).
% 0.98/1.21  thf('32', plain,
% 0.98/1.21      (![X43 : $i]:
% 0.98/1.21         ((m1_subset_1 @ (u1_pre_topc @ X43) @ 
% 0.98/1.21           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43))))
% 0.98/1.21          | ~ (l1_pre_topc @ X43))),
% 0.98/1.21      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.98/1.21  thf('33', plain,
% 0.98/1.21      (![X12 : $i, X13 : $i]:
% 0.98/1.21         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.98/1.21      inference('cnf', [status(esa)], [t3_subset])).
% 0.98/1.21  thf('34', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (~ (l1_pre_topc @ X0)
% 0.98/1.21          | (r1_tarski @ (u1_pre_topc @ X0) @ 
% 0.98/1.21             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.98/1.21      inference('sup-', [status(thm)], ['32', '33'])).
% 0.98/1.21  thf(t95_zfmisc_1, axiom,
% 0.98/1.21    (![A:$i,B:$i]:
% 0.98/1.21     ( ( r1_tarski @ A @ B ) =>
% 0.98/1.21       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.98/1.21  thf('35', plain,
% 0.98/1.21      (![X7 : $i, X8 : $i]:
% 0.98/1.21         ((r1_tarski @ (k3_tarski @ X7) @ (k3_tarski @ X8))
% 0.98/1.21          | ~ (r1_tarski @ X7 @ X8))),
% 0.98/1.21      inference('cnf', [status(esa)], [t95_zfmisc_1])).
% 0.98/1.21  thf('36', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (~ (l1_pre_topc @ X0)
% 0.98/1.21          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ 
% 0.98/1.21             (k3_tarski @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))),
% 0.98/1.21      inference('sup-', [status(thm)], ['34', '35'])).
% 0.98/1.21  thf('37', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         ((r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_struct_0 @ X0))
% 0.98/1.21          | ~ (l1_pre_topc @ X0)
% 0.98/1.21          | ~ (v2_pre_topc @ X0)
% 0.98/1.21          | ~ (l1_pre_topc @ X0))),
% 0.98/1.21      inference('sup+', [status(thm)], ['31', '36'])).
% 0.98/1.21  thf('38', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (~ (v2_pre_topc @ X0)
% 0.98/1.21          | ~ (l1_pre_topc @ X0)
% 0.98/1.21          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_struct_0 @ X0)))),
% 0.98/1.21      inference('simplify', [status(thm)], ['37'])).
% 0.98/1.21  thf('39', plain,
% 0.98/1.21      (![X40 : $i]:
% 0.98/1.21         (~ (v2_pre_topc @ X40)
% 0.98/1.21          | (r2_hidden @ (u1_struct_0 @ X40) @ (u1_pre_topc @ X40))
% 0.98/1.21          | ~ (l1_pre_topc @ X40))),
% 0.98/1.21      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.98/1.21  thf('40', plain,
% 0.98/1.21      (![X3 : $i, X4 : $i]:
% 0.98/1.21         ((r1_tarski @ X3 @ (k3_tarski @ X4)) | ~ (r2_hidden @ X3 @ X4))),
% 0.98/1.21      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.98/1.21  thf('41', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (~ (l1_pre_topc @ X0)
% 0.98/1.21          | ~ (v2_pre_topc @ X0)
% 0.98/1.21          | (r1_tarski @ (u1_struct_0 @ X0) @ (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.98/1.21      inference('sup-', [status(thm)], ['39', '40'])).
% 0.98/1.21  thf('42', plain,
% 0.98/1.21      (![X0 : $i, X2 : $i]:
% 0.98/1.21         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.98/1.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.98/1.21  thf('43', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (~ (v2_pre_topc @ X0)
% 0.98/1.21          | ~ (l1_pre_topc @ X0)
% 0.98/1.21          | ~ (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ 
% 0.98/1.21               (u1_struct_0 @ X0))
% 0.98/1.21          | ((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ X0)))),
% 0.98/1.21      inference('sup-', [status(thm)], ['41', '42'])).
% 0.98/1.21  thf('44', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (~ (l1_pre_topc @ X0)
% 0.98/1.21          | ~ (v2_pre_topc @ X0)
% 0.98/1.21          | ((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ X0))
% 0.98/1.21          | ~ (l1_pre_topc @ X0)
% 0.98/1.21          | ~ (v2_pre_topc @ X0))),
% 0.98/1.21      inference('sup-', [status(thm)], ['38', '43'])).
% 0.98/1.21  thf('45', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ X0))
% 0.98/1.21          | ~ (v2_pre_topc @ X0)
% 0.98/1.21          | ~ (l1_pre_topc @ X0))),
% 0.98/1.21      inference('simplify', [status(thm)], ['44'])).
% 0.98/1.21  thf('46', plain,
% 0.98/1.21      (![X40 : $i]:
% 0.98/1.21         (~ (v2_pre_topc @ X40)
% 0.98/1.21          | (r2_hidden @ (u1_struct_0 @ X40) @ (u1_pre_topc @ X40))
% 0.98/1.21          | ~ (l1_pre_topc @ X40))),
% 0.98/1.21      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.98/1.21  thf('47', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ X0))
% 0.98/1.21          | ~ (v2_pre_topc @ X0)
% 0.98/1.21          | ~ (l1_pre_topc @ X0))),
% 0.98/1.21      inference('simplify', [status(thm)], ['44'])).
% 0.98/1.21  thf(t14_yellow_1, axiom,
% 0.98/1.21    (![A:$i]:
% 0.98/1.21     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.98/1.21       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.98/1.21         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.98/1.21  thf('48', plain,
% 0.98/1.21      (![X44 : $i]:
% 0.98/1.21         (~ (r2_hidden @ (k3_tarski @ X44) @ X44)
% 0.98/1.21          | ((k4_yellow_0 @ (k2_yellow_1 @ X44)) = (k3_tarski @ X44))
% 0.98/1.21          | (v1_xboole_0 @ X44))),
% 0.98/1.21      inference('cnf', [status(esa)], [t14_yellow_1])).
% 0.98/1.21  thf('49', plain,
% 0.98/1.21      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.98/1.21      inference('sup-', [status(thm)], ['13', '14'])).
% 0.98/1.21  thf('50', plain,
% 0.98/1.21      (![X44 : $i]:
% 0.98/1.21         (((k4_yellow_0 @ (k2_yellow_1 @ X44)) = (k3_tarski @ X44))
% 0.98/1.21          | ~ (r2_hidden @ (k3_tarski @ X44) @ X44))),
% 0.98/1.21      inference('clc', [status(thm)], ['48', '49'])).
% 0.98/1.21  thf('51', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.98/1.21          | ~ (l1_pre_topc @ X0)
% 0.98/1.21          | ~ (v2_pre_topc @ X0)
% 0.98/1.21          | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 0.98/1.21              = (k3_tarski @ (u1_pre_topc @ X0))))),
% 0.98/1.21      inference('sup-', [status(thm)], ['47', '50'])).
% 0.98/1.21  thf('52', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (~ (l1_pre_topc @ X0)
% 0.98/1.21          | ~ (v2_pre_topc @ X0)
% 0.98/1.21          | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 0.98/1.21              = (k3_tarski @ (u1_pre_topc @ X0)))
% 0.98/1.21          | ~ (v2_pre_topc @ X0)
% 0.98/1.21          | ~ (l1_pre_topc @ X0))),
% 0.98/1.21      inference('sup-', [status(thm)], ['46', '51'])).
% 0.98/1.21  thf('53', plain,
% 0.98/1.21      (![X0 : $i]:
% 0.98/1.21         (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 0.98/1.21            = (k3_tarski @ (u1_pre_topc @ X0)))
% 0.98/1.21          | ~ (v2_pre_topc @ X0)
% 0.98/1.21          | ~ (l1_pre_topc @ X0))),
% 0.98/1.21      inference('simplify', [status(thm)], ['52'])).
% 0.98/1.21  thf(t24_yellow_1, conjecture,
% 0.98/1.21    (![A:$i]:
% 0.98/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.98/1.21       ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.98/1.21         ( u1_struct_0 @ A ) ) ))).
% 0.98/1.21  thf(zf_stmt_13, negated_conjecture,
% 0.98/1.21    (~( ![A:$i]:
% 0.98/1.21        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.98/1.21            ( l1_pre_topc @ A ) ) =>
% 0.98/1.21          ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.98/1.21            ( u1_struct_0 @ A ) ) ) )),
% 0.98/1.21    inference('cnf.neg', [status(esa)], [t24_yellow_1])).
% 0.98/1.21  thf('54', plain,
% 0.98/1.21      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 0.98/1.21         != (u1_struct_0 @ sk_A))),
% 0.98/1.21      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.98/1.21  thf('55', plain,
% 0.98/1.21      ((((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))
% 0.98/1.21        | ~ (l1_pre_topc @ sk_A)
% 0.98/1.21        | ~ (v2_pre_topc @ sk_A))),
% 0.98/1.21      inference('sup-', [status(thm)], ['53', '54'])).
% 0.98/1.21  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.98/1.21      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.98/1.21  thf('57', plain, ((v2_pre_topc @ sk_A)),
% 0.98/1.21      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.98/1.21  thf('58', plain,
% 0.98/1.21      (((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))),
% 0.98/1.21      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.98/1.21  thf('59', plain,
% 0.98/1.21      ((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.98/1.21        | ~ (l1_pre_topc @ sk_A)
% 0.98/1.21        | ~ (v2_pre_topc @ sk_A))),
% 0.98/1.21      inference('sup-', [status(thm)], ['45', '58'])).
% 0.98/1.21  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.98/1.21      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.98/1.21  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 0.98/1.21      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.98/1.21  thf('62', plain, (((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))),
% 0.98/1.21      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.98/1.21  thf('63', plain, ($false), inference('simplify', [status(thm)], ['62'])).
% 0.98/1.21  
% 0.98/1.21  % SZS output end Refutation
% 0.98/1.21  
% 0.98/1.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
