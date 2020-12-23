%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZBuJsiGf1a

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:19 EST 2020

% Result     : Theorem 18.31s
% Output     : Refutation 18.31s
% Verified   : 
% Statistics : Number of formulae       :  199 ( 770 expanded)
%              Number of leaves         :   52 ( 251 expanded)
%              Depth                    :   31
%              Number of atoms          : 1678 (7610 expanded)
%              Number of equality atoms :   60 ( 345 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

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
    ! [X51: $i] :
      ( ~ ( v2_pre_topc @ X51 )
      | ( r2_hidden @ ( u1_struct_0 @ X51 ) @ ( u1_pre_topc @ X51 ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
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

thf(t56_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B )
        & ( r2_hidden @ C @ A ) )
     => ( r1_tarski @ C @ B ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ X21 ) @ X22 )
      | ~ ( r2_hidden @ X23 @ X21 )
      | ( r1_tarski @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t56_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k3_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf(d12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_setfam_1 @ B @ A )
    <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_setfam_1 @ X18 @ X16 )
      | ~ ( r1_tarski @ X16 @ ( k3_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_setfam_1 @ ( u1_pre_topc @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X54: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X54 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) ) )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t60_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( m1_setfam_1 @ B @ A )
      <=> ( ( k5_setfam_1 @ A @ B )
          = A ) ) ) )).

thf('9',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_setfam_1 @ X28 @ X27 )
      | ( ( k5_setfam_1 @ X27 @ X28 )
        = X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[t60_setfam_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( m1_setfam_1 @ ( u1_pre_topc @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X54: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X54 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) ) )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(redefinition_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k5_setfam_1 @ A @ B )
        = ( k3_tarski @ B ) ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k5_setfam_1 @ X20 @ X19 )
        = ( k3_tarski @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('20',plain,(
    ! [X51: $i,X53: $i] :
      ( ~ ( v2_pre_topc @ X51 )
      | ( zip_tseitin_5 @ X53 @ X51 )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('21',plain,(
    ! [X54: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X54 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) ) )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('22',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) ) )
      | ( zip_tseitin_4 @ X48 @ X49 )
      | ~ ( zip_tseitin_5 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( zip_tseitin_5 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('27',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r1_tarski @ X45 @ ( u1_pre_topc @ X46 ) )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X46 ) @ X45 ) @ ( u1_pre_topc @ X46 ) )
      | ~ ( zip_tseitin_4 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('32',plain,(
    ! [X55: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X55 ) @ X55 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X55 ) )
        = ( k3_tarski @ X55 ) )
      | ( v1_xboole_0 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_pre_topc @ X0 ) )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

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

thf('34',plain,(
    ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('35',plain,
    ( ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
     != ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('38',plain,
    ( ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
     != ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('41',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('42',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    v1_xboole_0 @ ( u1_pre_topc @ sk_A ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('45',plain,(
    v1_xboole_0 @ ( u1_pre_topc @ sk_A ) ),
    inference(simplify,[status(thm)],['42'])).

thf('46',plain,(
    ! [X51: $i] :
      ( ~ ( v2_pre_topc @ X51 )
      | ( r2_hidden @ ( u1_struct_0 @ X51 ) @ ( u1_pre_topc @ X51 ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('47',plain,(
    ! [X12: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('48',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ ( sk_D_1 @ X7 @ X4 ) @ X4 )
      | ( X6
       != ( k3_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('49',plain,(
    ! [X4: $i,X7: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X7 @ X4 ) @ X4 )
      | ~ ( r2_hidden @ X7 @ ( k3_tarski @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['46','50'])).

thf('52',plain,(
    ! [X4: $i,X8: $i] :
      ( ( X8
        = ( k3_tarski @ X4 ) )
      | ( r2_hidden @ ( sk_C @ X8 @ X4 ) @ ( sk_D @ X8 @ X4 ) )
      | ( r2_hidden @ ( sk_C @ X8 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('53',plain,(
    ! [X4: $i,X8: $i] :
      ( ( X8
        = ( k3_tarski @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X4 ) @ X4 )
      | ( r2_hidden @ ( sk_C @ X8 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('54',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( m1_subset_1 @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k3_tarski @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('56',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( X1
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( sk_D @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X12: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( sk_D @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X1 )
      | ( X1
        = ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X1 )
      | ( X1 = X0 )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','59'])).

thf('61',plain,(
    ! [X12: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X1 )
      | ( X1 = X0 )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('65',plain,(
    ! [X4: $i,X8: $i,X9: $i] :
      ( ( X8
        = ( k3_tarski @ X4 ) )
      | ~ ( r2_hidden @ ( sk_C @ X8 @ X4 ) @ X9 )
      | ~ ( r2_hidden @ X9 @ X4 )
      | ~ ( r2_hidden @ ( sk_C @ X8 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k1_zfmisc_1 @ X1 ) ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( X0
        = ( k3_tarski @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X12: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k1_zfmisc_1 @ X1 ) ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( X0 = X1 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k1_zfmisc_1 @ X1 ) ) @ X0 )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( X0 = X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['63','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_D_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_pre_topc @ X0 ) )
      | ~ ( v1_xboole_0 @ ( u1_pre_topc @ X0 ) )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['51','71'])).

thf('73',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) )
    | ( ( sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) )
      = ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['45','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) )
    | ( ( sk_D_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) )
      = ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ! [X51: $i] :
      ( ~ ( v2_pre_topc @ X51 )
      | ( r2_hidden @ ( u1_struct_0 @ X51 ) @ ( u1_pre_topc @ X51 ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('78',plain,(
    ! [X12: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('79',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ ( sk_D_1 @ X7 @ X4 ) )
      | ( X6
       != ( k3_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('80',plain,(
    ! [X4: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ ( sk_D_1 @ X7 @ X4 ) )
      | ~ ( r2_hidden @ X7 @ ( k3_tarski @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( sk_D_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['78','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( sk_D_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['77','81'])).

thf('83',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['76','82'])).

thf('84',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('86',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('88',plain,(
    ! [X48: $i,X50: $i] :
      ( ( zip_tseitin_5 @ X48 @ X50 )
      | ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('89',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k5_setfam_1 @ X20 @ X19 )
        = ( k3_tarski @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_5 @ X1 @ X0 )
      | ( ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ X1 )
        = ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X45: $i,X47: $i] :
      ( ( zip_tseitin_4 @ X45 @ X47 )
      | ~ ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X47 ) @ X45 ) @ ( u1_pre_topc @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X0 ) @ ( u1_pre_topc @ X1 ) )
      | ( zip_tseitin_5 @ X0 @ X1 )
      | ( zip_tseitin_4 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X48: $i,X50: $i] :
      ( ( zip_tseitin_5 @ X48 @ X50 )
      | ~ ( zip_tseitin_4 @ X48 @ X50 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_5 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k3_tarski @ X0 ) @ ( u1_pre_topc @ X1 ) ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( zip_tseitin_5 @ ( u1_pre_topc @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['87','94'])).

thf('96',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) )
    | ( zip_tseitin_5 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['86','95'])).

thf('97',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('99',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) )
    | ( zip_tseitin_5 @ ( u1_pre_topc @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_xboole_0 @ X15 )
      | ( m1_subset_1 @ X15 @ X14 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('101',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_5 @ ( u1_pre_topc @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,(
    v1_xboole_0 @ ( u1_pre_topc @ sk_A ) ),
    inference(simplify,[status(thm)],['42'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_5 @ ( u1_pre_topc @ sk_A ) @ sk_A )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_pre_topc @ X0 ) )
      | ( zip_tseitin_5 @ ( u1_pre_topc @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','105'])).

thf('107',plain,
    ( ( zip_tseitin_5 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['43','106'])).

thf('108',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('110',plain,(
    zip_tseitin_5 @ ( u1_pre_topc @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( zip_tseitin_5 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('112',plain,
    ( ( zip_tseitin_4 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('114',plain,(
    zip_tseitin_4 @ ( u1_pre_topc @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('116',plain,(
    r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['12','116'])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('119',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('120',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,(
    v1_xboole_0 @ ( u1_pre_topc @ sk_A ) ),
    inference(simplify,[status(thm)],['42'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k3_tarski @ ( u1_pre_topc @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( sk_D_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['78','80'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r2_hidden @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( sk_D_1 @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( sk_D_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['122','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( sk_D_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['46','50'])).

thf('129',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( m1_subset_1 @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_pre_topc @ X0 ) ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_pre_topc @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( sk_D_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_pre_topc @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_pre_topc @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['127','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v1_xboole_0 @ ( u1_pre_topc @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['121','134'])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('137',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('138',plain,(
    v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    v1_xboole_0 @ ( u1_pre_topc @ sk_A ) ),
    inference(simplify,[status(thm)],['42'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    ~ ( v1_xboole_0 @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','142'])).

thf('144',plain,(
    v1_xboole_0 @ ( u1_pre_topc @ sk_A ) ),
    inference(simplify,[status(thm)],['42'])).

thf('145',plain,(
    $false ),
    inference(demod,[status(thm)],['143','144'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZBuJsiGf1a
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:08:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 18.31/18.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 18.31/18.51  % Solved by: fo/fo7.sh
% 18.31/18.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 18.31/18.51  % done 8988 iterations in 18.042s
% 18.31/18.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 18.31/18.51  % SZS output start Refutation
% 18.31/18.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 18.31/18.51  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 18.31/18.51  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 18.31/18.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 18.31/18.51  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 18.31/18.51  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 18.31/18.51  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 18.31/18.51  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 18.31/18.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 18.31/18.51  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 18.31/18.51  thf(sk_A_type, type, sk_A: $i).
% 18.31/18.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 18.31/18.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 18.31/18.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 18.31/18.51  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 18.31/18.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 18.31/18.51  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 18.31/18.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 18.31/18.51  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 18.31/18.51  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 18.31/18.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 18.31/18.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 18.31/18.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 18.31/18.51  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 18.31/18.51  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 18.31/18.51  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 18.31/18.51  thf(d1_pre_topc, axiom,
% 18.31/18.51    (![A:$i]:
% 18.31/18.51     ( ( l1_pre_topc @ A ) =>
% 18.31/18.51       ( ( v2_pre_topc @ A ) <=>
% 18.31/18.51         ( ( ![B:$i]:
% 18.31/18.51             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 18.31/18.51               ( ![C:$i]:
% 18.31/18.51                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 18.31/18.51                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 18.31/18.51                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 18.31/18.51                     ( r2_hidden @
% 18.31/18.51                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 18.31/18.51                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 18.31/18.51           ( ![B:$i]:
% 18.31/18.51             ( ( m1_subset_1 @
% 18.31/18.51                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 18.31/18.51               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 18.31/18.51                 ( r2_hidden @
% 18.31/18.51                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 18.31/18.51                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 18.31/18.51           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 18.31/18.51  thf(zf_stmt_0, type, zip_tseitin_5 : $i > $i > $o).
% 18.31/18.51  thf(zf_stmt_1, axiom,
% 18.31/18.51    (![B:$i,A:$i]:
% 18.31/18.51     ( ( zip_tseitin_5 @ B @ A ) <=>
% 18.31/18.51       ( ( m1_subset_1 @
% 18.31/18.51           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 18.31/18.51         ( zip_tseitin_4 @ B @ A ) ) ))).
% 18.31/18.51  thf(zf_stmt_2, type, zip_tseitin_4 : $i > $i > $o).
% 18.31/18.51  thf(zf_stmt_3, axiom,
% 18.31/18.51    (![B:$i,A:$i]:
% 18.31/18.51     ( ( zip_tseitin_4 @ B @ A ) <=>
% 18.31/18.51       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 18.31/18.51         ( r2_hidden @
% 18.31/18.51           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 18.31/18.51  thf(zf_stmt_4, type, zip_tseitin_3 : $i > $i > $o).
% 18.31/18.51  thf(zf_stmt_5, axiom,
% 18.31/18.51    (![B:$i,A:$i]:
% 18.31/18.51     ( ( zip_tseitin_3 @ B @ A ) <=>
% 18.31/18.51       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 18.31/18.51         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 18.31/18.51  thf(zf_stmt_6, type, zip_tseitin_2 : $i > $i > $i > $o).
% 18.31/18.51  thf(zf_stmt_7, axiom,
% 18.31/18.51    (![C:$i,B:$i,A:$i]:
% 18.31/18.51     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 18.31/18.51       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 18.31/18.51         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 18.31/18.51  thf(zf_stmt_8, type, zip_tseitin_1 : $i > $i > $i > $o).
% 18.31/18.51  thf(zf_stmt_9, axiom,
% 18.31/18.51    (![C:$i,B:$i,A:$i]:
% 18.31/18.51     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 18.31/18.51       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 18.31/18.51         ( r2_hidden @
% 18.31/18.51           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 18.31/18.51  thf(zf_stmt_10, type, zip_tseitin_0 : $i > $i > $i > $o).
% 18.31/18.51  thf(zf_stmt_11, axiom,
% 18.31/18.51    (![C:$i,B:$i,A:$i]:
% 18.31/18.51     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 18.31/18.51       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 18.31/18.51         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 18.31/18.51  thf(zf_stmt_12, axiom,
% 18.31/18.51    (![A:$i]:
% 18.31/18.51     ( ( l1_pre_topc @ A ) =>
% 18.31/18.51       ( ( v2_pre_topc @ A ) <=>
% 18.31/18.51         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 18.31/18.51           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 18.31/18.51           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 18.31/18.51  thf('0', plain,
% 18.31/18.51      (![X51 : $i]:
% 18.31/18.51         (~ (v2_pre_topc @ X51)
% 18.31/18.51          | (r2_hidden @ (u1_struct_0 @ X51) @ (u1_pre_topc @ X51))
% 18.31/18.51          | ~ (l1_pre_topc @ X51))),
% 18.31/18.51      inference('cnf', [status(esa)], [zf_stmt_12])).
% 18.31/18.51  thf(d10_xboole_0, axiom,
% 18.31/18.51    (![A:$i,B:$i]:
% 18.31/18.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 18.31/18.51  thf('1', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 18.31/18.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 18.31/18.51  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 18.31/18.51      inference('simplify', [status(thm)], ['1'])).
% 18.31/18.51  thf(t56_setfam_1, axiom,
% 18.31/18.51    (![A:$i,B:$i,C:$i]:
% 18.31/18.51     ( ( ( r1_tarski @ ( k3_tarski @ A ) @ B ) & ( r2_hidden @ C @ A ) ) =>
% 18.31/18.51       ( r1_tarski @ C @ B ) ))).
% 18.31/18.51  thf('3', plain,
% 18.31/18.51      (![X21 : $i, X22 : $i, X23 : $i]:
% 18.31/18.51         (~ (r1_tarski @ (k3_tarski @ X21) @ X22)
% 18.31/18.51          | ~ (r2_hidden @ X23 @ X21)
% 18.31/18.51          | (r1_tarski @ X23 @ X22))),
% 18.31/18.51      inference('cnf', [status(esa)], [t56_setfam_1])).
% 18.31/18.51  thf('4', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i]:
% 18.31/18.51         ((r1_tarski @ X1 @ (k3_tarski @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 18.31/18.51      inference('sup-', [status(thm)], ['2', '3'])).
% 18.31/18.51  thf('5', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (l1_pre_topc @ X0)
% 18.31/18.51          | ~ (v2_pre_topc @ X0)
% 18.31/18.51          | (r1_tarski @ (u1_struct_0 @ X0) @ (k3_tarski @ (u1_pre_topc @ X0))))),
% 18.31/18.51      inference('sup-', [status(thm)], ['0', '4'])).
% 18.31/18.51  thf(d12_setfam_1, axiom,
% 18.31/18.51    (![A:$i,B:$i]:
% 18.31/18.51     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 18.31/18.51  thf('6', plain,
% 18.31/18.51      (![X16 : $i, X18 : $i]:
% 18.31/18.51         ((m1_setfam_1 @ X18 @ X16) | ~ (r1_tarski @ X16 @ (k3_tarski @ X18)))),
% 18.31/18.51      inference('cnf', [status(esa)], [d12_setfam_1])).
% 18.31/18.51  thf('7', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (v2_pre_topc @ X0)
% 18.31/18.51          | ~ (l1_pre_topc @ X0)
% 18.31/18.51          | (m1_setfam_1 @ (u1_pre_topc @ X0) @ (u1_struct_0 @ X0)))),
% 18.31/18.51      inference('sup-', [status(thm)], ['5', '6'])).
% 18.31/18.51  thf(dt_u1_pre_topc, axiom,
% 18.31/18.51    (![A:$i]:
% 18.31/18.51     ( ( l1_pre_topc @ A ) =>
% 18.31/18.51       ( m1_subset_1 @
% 18.31/18.51         ( u1_pre_topc @ A ) @ 
% 18.31/18.51         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 18.31/18.51  thf('8', plain,
% 18.31/18.51      (![X54 : $i]:
% 18.31/18.51         ((m1_subset_1 @ (u1_pre_topc @ X54) @ 
% 18.31/18.51           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54))))
% 18.31/18.51          | ~ (l1_pre_topc @ X54))),
% 18.31/18.51      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 18.31/18.51  thf(t60_setfam_1, axiom,
% 18.31/18.51    (![A:$i,B:$i]:
% 18.31/18.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 18.31/18.51       ( ( m1_setfam_1 @ B @ A ) <=> ( ( k5_setfam_1 @ A @ B ) = ( A ) ) ) ))).
% 18.31/18.51  thf('9', plain,
% 18.31/18.51      (![X27 : $i, X28 : $i]:
% 18.31/18.51         (~ (m1_setfam_1 @ X28 @ X27)
% 18.31/18.51          | ((k5_setfam_1 @ X27 @ X28) = (X27))
% 18.31/18.51          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X27))))),
% 18.31/18.51      inference('cnf', [status(esa)], [t60_setfam_1])).
% 18.31/18.51  thf('10', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (l1_pre_topc @ X0)
% 18.31/18.51          | ((k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 18.31/18.51              = (u1_struct_0 @ X0))
% 18.31/18.51          | ~ (m1_setfam_1 @ (u1_pre_topc @ X0) @ (u1_struct_0 @ X0)))),
% 18.31/18.51      inference('sup-', [status(thm)], ['8', '9'])).
% 18.31/18.51  thf('11', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (l1_pre_topc @ X0)
% 18.31/18.51          | ~ (v2_pre_topc @ X0)
% 18.31/18.51          | ((k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 18.31/18.51              = (u1_struct_0 @ X0))
% 18.31/18.51          | ~ (l1_pre_topc @ X0))),
% 18.31/18.51      inference('sup-', [status(thm)], ['7', '10'])).
% 18.31/18.51  thf('12', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (((k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 18.31/18.51            = (u1_struct_0 @ X0))
% 18.31/18.51          | ~ (v2_pre_topc @ X0)
% 18.31/18.51          | ~ (l1_pre_topc @ X0))),
% 18.31/18.51      inference('simplify', [status(thm)], ['11'])).
% 18.31/18.51  thf('13', plain,
% 18.31/18.51      (![X54 : $i]:
% 18.31/18.51         ((m1_subset_1 @ (u1_pre_topc @ X54) @ 
% 18.31/18.51           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54))))
% 18.31/18.51          | ~ (l1_pre_topc @ X54))),
% 18.31/18.51      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 18.31/18.51  thf(redefinition_k5_setfam_1, axiom,
% 18.31/18.51    (![A:$i,B:$i]:
% 18.31/18.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 18.31/18.51       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 18.31/18.51  thf('14', plain,
% 18.31/18.51      (![X19 : $i, X20 : $i]:
% 18.31/18.51         (((k5_setfam_1 @ X20 @ X19) = (k3_tarski @ X19))
% 18.31/18.51          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 18.31/18.51      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 18.31/18.51  thf('15', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (l1_pre_topc @ X0)
% 18.31/18.51          | ((k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 18.31/18.51              = (k3_tarski @ (u1_pre_topc @ X0))))),
% 18.31/18.51      inference('sup-', [status(thm)], ['13', '14'])).
% 18.31/18.51  thf('16', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (((k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 18.31/18.51            = (u1_struct_0 @ X0))
% 18.31/18.51          | ~ (v2_pre_topc @ X0)
% 18.31/18.51          | ~ (l1_pre_topc @ X0))),
% 18.31/18.51      inference('simplify', [status(thm)], ['11'])).
% 18.31/18.51  thf('17', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ X0))
% 18.31/18.51          | ~ (l1_pre_topc @ X0)
% 18.31/18.51          | ~ (l1_pre_topc @ X0)
% 18.31/18.51          | ~ (v2_pre_topc @ X0))),
% 18.31/18.51      inference('sup+', [status(thm)], ['15', '16'])).
% 18.31/18.51  thf('18', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (v2_pre_topc @ X0)
% 18.31/18.51          | ~ (l1_pre_topc @ X0)
% 18.31/18.51          | ((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ X0)))),
% 18.31/18.51      inference('simplify', [status(thm)], ['17'])).
% 18.31/18.51  thf('19', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (l1_pre_topc @ X0)
% 18.31/18.51          | ((k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 18.31/18.51              = (k3_tarski @ (u1_pre_topc @ X0))))),
% 18.31/18.51      inference('sup-', [status(thm)], ['13', '14'])).
% 18.31/18.51  thf('20', plain,
% 18.31/18.51      (![X51 : $i, X53 : $i]:
% 18.31/18.51         (~ (v2_pre_topc @ X51)
% 18.31/18.51          | (zip_tseitin_5 @ X53 @ X51)
% 18.31/18.51          | ~ (l1_pre_topc @ X51))),
% 18.31/18.51      inference('cnf', [status(esa)], [zf_stmt_12])).
% 18.31/18.51  thf('21', plain,
% 18.31/18.51      (![X54 : $i]:
% 18.31/18.51         ((m1_subset_1 @ (u1_pre_topc @ X54) @ 
% 18.31/18.51           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54))))
% 18.31/18.51          | ~ (l1_pre_topc @ X54))),
% 18.31/18.51      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 18.31/18.51  thf('22', plain,
% 18.31/18.51      (![X48 : $i, X49 : $i]:
% 18.31/18.51         (~ (m1_subset_1 @ X48 @ 
% 18.31/18.51             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49))))
% 18.31/18.51          | (zip_tseitin_4 @ X48 @ X49)
% 18.31/18.51          | ~ (zip_tseitin_5 @ X48 @ X49))),
% 18.31/18.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 18.31/18.51  thf('23', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (l1_pre_topc @ X0)
% 18.31/18.51          | ~ (zip_tseitin_5 @ (u1_pre_topc @ X0) @ X0)
% 18.31/18.51          | (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0))),
% 18.31/18.51      inference('sup-', [status(thm)], ['21', '22'])).
% 18.31/18.51  thf('24', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (l1_pre_topc @ X0)
% 18.31/18.51          | ~ (v2_pre_topc @ X0)
% 18.31/18.51          | (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0)
% 18.31/18.51          | ~ (l1_pre_topc @ X0))),
% 18.31/18.51      inference('sup-', [status(thm)], ['20', '23'])).
% 18.31/18.51  thf('25', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         ((zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0)
% 18.31/18.51          | ~ (v2_pre_topc @ X0)
% 18.31/18.51          | ~ (l1_pre_topc @ X0))),
% 18.31/18.51      inference('simplify', [status(thm)], ['24'])).
% 18.31/18.51  thf('26', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 18.31/18.51      inference('simplify', [status(thm)], ['1'])).
% 18.31/18.51  thf('27', plain,
% 18.31/18.51      (![X45 : $i, X46 : $i]:
% 18.31/18.51         (~ (r1_tarski @ X45 @ (u1_pre_topc @ X46))
% 18.31/18.51          | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ X46) @ X45) @ 
% 18.31/18.51             (u1_pre_topc @ X46))
% 18.31/18.51          | ~ (zip_tseitin_4 @ X45 @ X46))),
% 18.31/18.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 18.31/18.51  thf('28', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0)
% 18.31/18.51          | (r2_hidden @ 
% 18.31/18.51             (k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 18.31/18.51             (u1_pre_topc @ X0)))),
% 18.31/18.51      inference('sup-', [status(thm)], ['26', '27'])).
% 18.31/18.51  thf('29', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (l1_pre_topc @ X0)
% 18.31/18.51          | ~ (v2_pre_topc @ X0)
% 18.31/18.51          | (r2_hidden @ 
% 18.31/18.51             (k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 18.31/18.51             (u1_pre_topc @ X0)))),
% 18.31/18.51      inference('sup-', [status(thm)], ['25', '28'])).
% 18.31/18.51  thf('30', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         ((r2_hidden @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_pre_topc @ X0))
% 18.31/18.51          | ~ (l1_pre_topc @ X0)
% 18.31/18.51          | ~ (v2_pre_topc @ X0)
% 18.31/18.51          | ~ (l1_pre_topc @ X0))),
% 18.31/18.51      inference('sup+', [status(thm)], ['19', '29'])).
% 18.31/18.51  thf('31', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (v2_pre_topc @ X0)
% 18.31/18.51          | ~ (l1_pre_topc @ X0)
% 18.31/18.51          | (r2_hidden @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_pre_topc @ X0)))),
% 18.31/18.51      inference('simplify', [status(thm)], ['30'])).
% 18.31/18.51  thf(t14_yellow_1, axiom,
% 18.31/18.51    (![A:$i]:
% 18.31/18.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 18.31/18.51       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 18.31/18.51         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 18.31/18.51  thf('32', plain,
% 18.31/18.51      (![X55 : $i]:
% 18.31/18.51         (~ (r2_hidden @ (k3_tarski @ X55) @ X55)
% 18.31/18.51          | ((k4_yellow_0 @ (k2_yellow_1 @ X55)) = (k3_tarski @ X55))
% 18.31/18.51          | (v1_xboole_0 @ X55))),
% 18.31/18.51      inference('cnf', [status(esa)], [t14_yellow_1])).
% 18.31/18.51  thf('33', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (l1_pre_topc @ X0)
% 18.31/18.51          | ~ (v2_pre_topc @ X0)
% 18.31/18.51          | (v1_xboole_0 @ (u1_pre_topc @ X0))
% 18.31/18.51          | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 18.31/18.51              = (k3_tarski @ (u1_pre_topc @ X0))))),
% 18.31/18.51      inference('sup-', [status(thm)], ['31', '32'])).
% 18.31/18.51  thf(t24_yellow_1, conjecture,
% 18.31/18.51    (![A:$i]:
% 18.31/18.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 18.31/18.51       ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 18.31/18.51         ( u1_struct_0 @ A ) ) ))).
% 18.31/18.51  thf(zf_stmt_13, negated_conjecture,
% 18.31/18.51    (~( ![A:$i]:
% 18.31/18.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 18.31/18.51            ( l1_pre_topc @ A ) ) =>
% 18.31/18.51          ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 18.31/18.51            ( u1_struct_0 @ A ) ) ) )),
% 18.31/18.51    inference('cnf.neg', [status(esa)], [t24_yellow_1])).
% 18.31/18.51  thf('34', plain,
% 18.31/18.51      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 18.31/18.51         != (u1_struct_0 @ sk_A))),
% 18.31/18.51      inference('cnf', [status(esa)], [zf_stmt_13])).
% 18.31/18.51  thf('35', plain,
% 18.31/18.51      ((((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))
% 18.31/18.51        | (v1_xboole_0 @ (u1_pre_topc @ sk_A))
% 18.31/18.51        | ~ (v2_pre_topc @ sk_A)
% 18.31/18.51        | ~ (l1_pre_topc @ sk_A))),
% 18.31/18.51      inference('sup-', [status(thm)], ['33', '34'])).
% 18.31/18.51  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 18.31/18.51      inference('cnf', [status(esa)], [zf_stmt_13])).
% 18.31/18.51  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 18.31/18.51      inference('cnf', [status(esa)], [zf_stmt_13])).
% 18.31/18.51  thf('38', plain,
% 18.31/18.51      ((((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))
% 18.31/18.51        | (v1_xboole_0 @ (u1_pre_topc @ sk_A)))),
% 18.31/18.51      inference('demod', [status(thm)], ['35', '36', '37'])).
% 18.31/18.51  thf('39', plain,
% 18.31/18.51      ((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 18.31/18.51        | ~ (l1_pre_topc @ sk_A)
% 18.31/18.51        | ~ (v2_pre_topc @ sk_A)
% 18.31/18.51        | (v1_xboole_0 @ (u1_pre_topc @ sk_A)))),
% 18.31/18.51      inference('sup-', [status(thm)], ['18', '38'])).
% 18.31/18.51  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 18.31/18.51      inference('cnf', [status(esa)], [zf_stmt_13])).
% 18.31/18.51  thf('41', plain, ((v2_pre_topc @ sk_A)),
% 18.31/18.51      inference('cnf', [status(esa)], [zf_stmt_13])).
% 18.31/18.51  thf('42', plain,
% 18.31/18.51      ((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 18.31/18.51        | (v1_xboole_0 @ (u1_pre_topc @ sk_A)))),
% 18.31/18.51      inference('demod', [status(thm)], ['39', '40', '41'])).
% 18.31/18.51  thf('43', plain, ((v1_xboole_0 @ (u1_pre_topc @ sk_A))),
% 18.31/18.51      inference('simplify', [status(thm)], ['42'])).
% 18.31/18.51  thf('44', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (v2_pre_topc @ X0)
% 18.31/18.51          | ~ (l1_pre_topc @ X0)
% 18.31/18.51          | (r2_hidden @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_pre_topc @ X0)))),
% 18.31/18.51      inference('simplify', [status(thm)], ['30'])).
% 18.31/18.51  thf('45', plain, ((v1_xboole_0 @ (u1_pre_topc @ sk_A))),
% 18.31/18.51      inference('simplify', [status(thm)], ['42'])).
% 18.31/18.51  thf('46', plain,
% 18.31/18.51      (![X51 : $i]:
% 18.31/18.51         (~ (v2_pre_topc @ X51)
% 18.31/18.51          | (r2_hidden @ (u1_struct_0 @ X51) @ (u1_pre_topc @ X51))
% 18.31/18.51          | ~ (l1_pre_topc @ X51))),
% 18.31/18.51      inference('cnf', [status(esa)], [zf_stmt_12])).
% 18.31/18.51  thf(t99_zfmisc_1, axiom,
% 18.31/18.51    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 18.31/18.51  thf('47', plain, (![X12 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X12)) = (X12))),
% 18.31/18.51      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 18.31/18.51  thf(d4_tarski, axiom,
% 18.31/18.51    (![A:$i,B:$i]:
% 18.31/18.51     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 18.31/18.51       ( ![C:$i]:
% 18.31/18.51         ( ( r2_hidden @ C @ B ) <=>
% 18.31/18.51           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 18.31/18.51  thf('48', plain,
% 18.31/18.51      (![X4 : $i, X6 : $i, X7 : $i]:
% 18.31/18.51         (~ (r2_hidden @ X7 @ X6)
% 18.31/18.51          | (r2_hidden @ (sk_D_1 @ X7 @ X4) @ X4)
% 18.31/18.51          | ((X6) != (k3_tarski @ X4)))),
% 18.31/18.51      inference('cnf', [status(esa)], [d4_tarski])).
% 18.31/18.51  thf('49', plain,
% 18.31/18.51      (![X4 : $i, X7 : $i]:
% 18.31/18.51         ((r2_hidden @ (sk_D_1 @ X7 @ X4) @ X4)
% 18.31/18.51          | ~ (r2_hidden @ X7 @ (k3_tarski @ X4)))),
% 18.31/18.51      inference('simplify', [status(thm)], ['48'])).
% 18.31/18.51  thf('50', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i]:
% 18.31/18.51         (~ (r2_hidden @ X1 @ X0)
% 18.31/18.51          | (r2_hidden @ (sk_D_1 @ X1 @ (k1_zfmisc_1 @ X0)) @ 
% 18.31/18.51             (k1_zfmisc_1 @ X0)))),
% 18.31/18.51      inference('sup-', [status(thm)], ['47', '49'])).
% 18.31/18.51  thf('51', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (l1_pre_topc @ X0)
% 18.31/18.51          | ~ (v2_pre_topc @ X0)
% 18.31/18.51          | (r2_hidden @ 
% 18.31/18.51             (sk_D_1 @ (u1_struct_0 @ X0) @ (k1_zfmisc_1 @ (u1_pre_topc @ X0))) @ 
% 18.31/18.51             (k1_zfmisc_1 @ (u1_pre_topc @ X0))))),
% 18.31/18.51      inference('sup-', [status(thm)], ['46', '50'])).
% 18.31/18.51  thf('52', plain,
% 18.31/18.51      (![X4 : $i, X8 : $i]:
% 18.31/18.51         (((X8) = (k3_tarski @ X4))
% 18.31/18.51          | (r2_hidden @ (sk_C @ X8 @ X4) @ (sk_D @ X8 @ X4))
% 18.31/18.51          | (r2_hidden @ (sk_C @ X8 @ X4) @ X8))),
% 18.31/18.51      inference('cnf', [status(esa)], [d4_tarski])).
% 18.31/18.51  thf('53', plain,
% 18.31/18.51      (![X4 : $i, X8 : $i]:
% 18.31/18.51         (((X8) = (k3_tarski @ X4))
% 18.31/18.51          | (r2_hidden @ (sk_D @ X8 @ X4) @ X4)
% 18.31/18.51          | (r2_hidden @ (sk_C @ X8 @ X4) @ X8))),
% 18.31/18.51      inference('cnf', [status(esa)], [d4_tarski])).
% 18.31/18.51  thf(d2_subset_1, axiom,
% 18.31/18.51    (![A:$i,B:$i]:
% 18.31/18.51     ( ( ( v1_xboole_0 @ A ) =>
% 18.31/18.51         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 18.31/18.51       ( ( ~( v1_xboole_0 @ A ) ) =>
% 18.31/18.51         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 18.31/18.51  thf('54', plain,
% 18.31/18.51      (![X13 : $i, X14 : $i]:
% 18.31/18.51         (~ (r2_hidden @ X13 @ X14)
% 18.31/18.51          | (m1_subset_1 @ X13 @ X14)
% 18.31/18.51          | (v1_xboole_0 @ X14))),
% 18.31/18.51      inference('cnf', [status(esa)], [d2_subset_1])).
% 18.31/18.51  thf('55', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i]:
% 18.31/18.51         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 18.31/18.51          | ((X1) = (k3_tarski @ X0))
% 18.31/18.51          | (v1_xboole_0 @ X0)
% 18.31/18.51          | (m1_subset_1 @ (sk_D @ X1 @ X0) @ X0))),
% 18.31/18.51      inference('sup-', [status(thm)], ['53', '54'])).
% 18.31/18.51  thf(t5_subset, axiom,
% 18.31/18.51    (![A:$i,B:$i,C:$i]:
% 18.31/18.51     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 18.31/18.51          ( v1_xboole_0 @ C ) ) ))).
% 18.31/18.51  thf('56', plain,
% 18.31/18.51      (![X24 : $i, X25 : $i, X26 : $i]:
% 18.31/18.51         (~ (r2_hidden @ X24 @ X25)
% 18.31/18.51          | ~ (v1_xboole_0 @ X26)
% 18.31/18.51          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 18.31/18.51      inference('cnf', [status(esa)], [t5_subset])).
% 18.31/18.51  thf('57', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.31/18.51         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 18.31/18.51          | ((X1) = (k3_tarski @ (k1_zfmisc_1 @ X0)))
% 18.31/18.51          | (r2_hidden @ (sk_C @ X1 @ (k1_zfmisc_1 @ X0)) @ X1)
% 18.31/18.51          | ~ (v1_xboole_0 @ X0)
% 18.31/18.51          | ~ (r2_hidden @ X2 @ (sk_D @ X1 @ (k1_zfmisc_1 @ X0))))),
% 18.31/18.51      inference('sup-', [status(thm)], ['55', '56'])).
% 18.31/18.51  thf('58', plain, (![X12 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X12)) = (X12))),
% 18.31/18.51      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 18.31/18.51  thf('59', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.31/18.51         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 18.31/18.51          | ((X1) = (X0))
% 18.31/18.51          | (r2_hidden @ (sk_C @ X1 @ (k1_zfmisc_1 @ X0)) @ X1)
% 18.31/18.51          | ~ (v1_xboole_0 @ X0)
% 18.31/18.51          | ~ (r2_hidden @ X2 @ (sk_D @ X1 @ (k1_zfmisc_1 @ X0))))),
% 18.31/18.51      inference('demod', [status(thm)], ['57', '58'])).
% 18.31/18.51  thf('60', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i]:
% 18.31/18.51         ((r2_hidden @ (sk_C @ X1 @ (k1_zfmisc_1 @ X0)) @ X1)
% 18.31/18.51          | ((X1) = (k3_tarski @ (k1_zfmisc_1 @ X0)))
% 18.31/18.51          | ~ (v1_xboole_0 @ X0)
% 18.31/18.51          | (r2_hidden @ (sk_C @ X1 @ (k1_zfmisc_1 @ X0)) @ X1)
% 18.31/18.51          | ((X1) = (X0))
% 18.31/18.51          | (v1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 18.31/18.51      inference('sup-', [status(thm)], ['52', '59'])).
% 18.31/18.51  thf('61', plain, (![X12 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X12)) = (X12))),
% 18.31/18.51      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 18.31/18.51  thf('62', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i]:
% 18.31/18.51         ((r2_hidden @ (sk_C @ X1 @ (k1_zfmisc_1 @ X0)) @ X1)
% 18.31/18.51          | ((X1) = (X0))
% 18.31/18.51          | ~ (v1_xboole_0 @ X0)
% 18.31/18.51          | (r2_hidden @ (sk_C @ X1 @ (k1_zfmisc_1 @ X0)) @ X1)
% 18.31/18.51          | ((X1) = (X0))
% 18.31/18.51          | (v1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 18.31/18.51      inference('demod', [status(thm)], ['60', '61'])).
% 18.31/18.51  thf('63', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i]:
% 18.31/18.51         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 18.31/18.51          | ~ (v1_xboole_0 @ X0)
% 18.31/18.51          | ((X1) = (X0))
% 18.31/18.51          | (r2_hidden @ (sk_C @ X1 @ (k1_zfmisc_1 @ X0)) @ X1))),
% 18.31/18.51      inference('simplify', [status(thm)], ['62'])).
% 18.31/18.51  thf('64', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i]:
% 18.31/18.51         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 18.31/18.51          | ~ (v1_xboole_0 @ X0)
% 18.31/18.51          | ((X1) = (X0))
% 18.31/18.51          | (r2_hidden @ (sk_C @ X1 @ (k1_zfmisc_1 @ X0)) @ X1))),
% 18.31/18.51      inference('simplify', [status(thm)], ['62'])).
% 18.31/18.51  thf('65', plain,
% 18.31/18.51      (![X4 : $i, X8 : $i, X9 : $i]:
% 18.31/18.51         (((X8) = (k3_tarski @ X4))
% 18.31/18.51          | ~ (r2_hidden @ (sk_C @ X8 @ X4) @ X9)
% 18.31/18.51          | ~ (r2_hidden @ X9 @ X4)
% 18.31/18.51          | ~ (r2_hidden @ (sk_C @ X8 @ X4) @ X8))),
% 18.31/18.51      inference('cnf', [status(esa)], [d4_tarski])).
% 18.31/18.51  thf('66', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i]:
% 18.31/18.51         (((X0) = (X1))
% 18.31/18.51          | ~ (v1_xboole_0 @ X1)
% 18.31/18.51          | (v1_xboole_0 @ (k1_zfmisc_1 @ X1))
% 18.31/18.51          | ~ (r2_hidden @ (sk_C @ X0 @ (k1_zfmisc_1 @ X1)) @ X0)
% 18.31/18.51          | ~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ X1))
% 18.31/18.51          | ((X0) = (k3_tarski @ (k1_zfmisc_1 @ X1))))),
% 18.31/18.51      inference('sup-', [status(thm)], ['64', '65'])).
% 18.31/18.51  thf('67', plain, (![X12 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X12)) = (X12))),
% 18.31/18.51      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 18.31/18.51  thf('68', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i]:
% 18.31/18.51         (((X0) = (X1))
% 18.31/18.51          | ~ (v1_xboole_0 @ X1)
% 18.31/18.51          | (v1_xboole_0 @ (k1_zfmisc_1 @ X1))
% 18.31/18.51          | ~ (r2_hidden @ (sk_C @ X0 @ (k1_zfmisc_1 @ X1)) @ X0)
% 18.31/18.51          | ~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ X1))
% 18.31/18.51          | ((X0) = (X1)))),
% 18.31/18.51      inference('demod', [status(thm)], ['66', '67'])).
% 18.31/18.51  thf('69', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i]:
% 18.31/18.51         (~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ X1))
% 18.31/18.51          | ~ (r2_hidden @ (sk_C @ X0 @ (k1_zfmisc_1 @ X1)) @ X0)
% 18.31/18.51          | (v1_xboole_0 @ (k1_zfmisc_1 @ X1))
% 18.31/18.51          | ~ (v1_xboole_0 @ X1)
% 18.31/18.51          | ((X0) = (X1)))),
% 18.31/18.51      inference('simplify', [status(thm)], ['68'])).
% 18.31/18.51  thf('70', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i]:
% 18.31/18.51         (((X0) = (X1))
% 18.31/18.51          | ~ (v1_xboole_0 @ X1)
% 18.31/18.51          | (v1_xboole_0 @ (k1_zfmisc_1 @ X1))
% 18.31/18.51          | ((X0) = (X1))
% 18.31/18.51          | ~ (v1_xboole_0 @ X1)
% 18.31/18.51          | (v1_xboole_0 @ (k1_zfmisc_1 @ X1))
% 18.31/18.51          | ~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ X1)))),
% 18.31/18.51      inference('sup-', [status(thm)], ['63', '69'])).
% 18.31/18.51  thf('71', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i]:
% 18.31/18.51         (~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ X1))
% 18.31/18.51          | (v1_xboole_0 @ (k1_zfmisc_1 @ X1))
% 18.31/18.51          | ~ (v1_xboole_0 @ X1)
% 18.31/18.51          | ((X0) = (X1)))),
% 18.31/18.51      inference('simplify', [status(thm)], ['70'])).
% 18.31/18.51  thf('72', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (v2_pre_topc @ X0)
% 18.31/18.51          | ~ (l1_pre_topc @ X0)
% 18.31/18.51          | ((sk_D_1 @ (u1_struct_0 @ X0) @ (k1_zfmisc_1 @ (u1_pre_topc @ X0)))
% 18.31/18.51              = (u1_pre_topc @ X0))
% 18.31/18.51          | ~ (v1_xboole_0 @ (u1_pre_topc @ X0))
% 18.31/18.51          | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_pre_topc @ X0))))),
% 18.31/18.51      inference('sup-', [status(thm)], ['51', '71'])).
% 18.31/18.51  thf('73', plain,
% 18.31/18.51      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_pre_topc @ sk_A)))
% 18.31/18.51        | ((sk_D_1 @ (u1_struct_0 @ sk_A) @ 
% 18.31/18.51            (k1_zfmisc_1 @ (u1_pre_topc @ sk_A))) = (u1_pre_topc @ sk_A))
% 18.31/18.51        | ~ (l1_pre_topc @ sk_A)
% 18.31/18.51        | ~ (v2_pre_topc @ sk_A))),
% 18.31/18.51      inference('sup-', [status(thm)], ['45', '72'])).
% 18.31/18.51  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 18.31/18.51      inference('cnf', [status(esa)], [zf_stmt_13])).
% 18.31/18.51  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 18.31/18.51      inference('cnf', [status(esa)], [zf_stmt_13])).
% 18.31/18.51  thf('76', plain,
% 18.31/18.51      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_pre_topc @ sk_A)))
% 18.31/18.51        | ((sk_D_1 @ (u1_struct_0 @ sk_A) @ 
% 18.31/18.51            (k1_zfmisc_1 @ (u1_pre_topc @ sk_A))) = (u1_pre_topc @ sk_A)))),
% 18.31/18.51      inference('demod', [status(thm)], ['73', '74', '75'])).
% 18.31/18.51  thf('77', plain,
% 18.31/18.51      (![X51 : $i]:
% 18.31/18.51         (~ (v2_pre_topc @ X51)
% 18.31/18.51          | (r2_hidden @ (u1_struct_0 @ X51) @ (u1_pre_topc @ X51))
% 18.31/18.51          | ~ (l1_pre_topc @ X51))),
% 18.31/18.51      inference('cnf', [status(esa)], [zf_stmt_12])).
% 18.31/18.51  thf('78', plain, (![X12 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X12)) = (X12))),
% 18.31/18.51      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 18.31/18.51  thf('79', plain,
% 18.31/18.51      (![X4 : $i, X6 : $i, X7 : $i]:
% 18.31/18.51         (~ (r2_hidden @ X7 @ X6)
% 18.31/18.51          | (r2_hidden @ X7 @ (sk_D_1 @ X7 @ X4))
% 18.31/18.51          | ((X6) != (k3_tarski @ X4)))),
% 18.31/18.51      inference('cnf', [status(esa)], [d4_tarski])).
% 18.31/18.51  thf('80', plain,
% 18.31/18.51      (![X4 : $i, X7 : $i]:
% 18.31/18.51         ((r2_hidden @ X7 @ (sk_D_1 @ X7 @ X4))
% 18.31/18.51          | ~ (r2_hidden @ X7 @ (k3_tarski @ X4)))),
% 18.31/18.51      inference('simplify', [status(thm)], ['79'])).
% 18.31/18.51  thf('81', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i]:
% 18.31/18.51         (~ (r2_hidden @ X1 @ X0)
% 18.31/18.51          | (r2_hidden @ X1 @ (sk_D_1 @ X1 @ (k1_zfmisc_1 @ X0))))),
% 18.31/18.51      inference('sup-', [status(thm)], ['78', '80'])).
% 18.31/18.51  thf('82', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (l1_pre_topc @ X0)
% 18.31/18.51          | ~ (v2_pre_topc @ X0)
% 18.31/18.51          | (r2_hidden @ (u1_struct_0 @ X0) @ 
% 18.31/18.51             (sk_D_1 @ (u1_struct_0 @ X0) @ (k1_zfmisc_1 @ (u1_pre_topc @ X0)))))),
% 18.31/18.51      inference('sup-', [status(thm)], ['77', '81'])).
% 18.31/18.51  thf('83', plain,
% 18.31/18.51      (((r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 18.31/18.51        | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_pre_topc @ sk_A)))
% 18.31/18.51        | ~ (v2_pre_topc @ sk_A)
% 18.31/18.51        | ~ (l1_pre_topc @ sk_A))),
% 18.31/18.51      inference('sup+', [status(thm)], ['76', '82'])).
% 18.31/18.51  thf('84', plain, ((v2_pre_topc @ sk_A)),
% 18.31/18.51      inference('cnf', [status(esa)], [zf_stmt_13])).
% 18.31/18.51  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 18.31/18.51      inference('cnf', [status(esa)], [zf_stmt_13])).
% 18.31/18.51  thf('86', plain,
% 18.31/18.51      (((r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 18.31/18.51        | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_pre_topc @ sk_A))))),
% 18.31/18.51      inference('demod', [status(thm)], ['83', '84', '85'])).
% 18.31/18.51  thf('87', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (v2_pre_topc @ X0)
% 18.31/18.51          | ~ (l1_pre_topc @ X0)
% 18.31/18.51          | ((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ X0)))),
% 18.31/18.51      inference('simplify', [status(thm)], ['17'])).
% 18.31/18.51  thf('88', plain,
% 18.31/18.51      (![X48 : $i, X50 : $i]:
% 18.31/18.51         ((zip_tseitin_5 @ X48 @ X50)
% 18.31/18.51          | (m1_subset_1 @ X48 @ 
% 18.31/18.51             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))))),
% 18.31/18.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 18.31/18.51  thf('89', plain,
% 18.31/18.51      (![X19 : $i, X20 : $i]:
% 18.31/18.51         (((k5_setfam_1 @ X20 @ X19) = (k3_tarski @ X19))
% 18.31/18.51          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X20))))),
% 18.31/18.51      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 18.31/18.51  thf('90', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i]:
% 18.31/18.51         ((zip_tseitin_5 @ X1 @ X0)
% 18.31/18.51          | ((k5_setfam_1 @ (u1_struct_0 @ X0) @ X1) = (k3_tarski @ X1)))),
% 18.31/18.51      inference('sup-', [status(thm)], ['88', '89'])).
% 18.31/18.51  thf('91', plain,
% 18.31/18.51      (![X45 : $i, X47 : $i]:
% 18.31/18.51         ((zip_tseitin_4 @ X45 @ X47)
% 18.31/18.51          | ~ (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ X47) @ X45) @ 
% 18.31/18.51               (u1_pre_topc @ X47)))),
% 18.31/18.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 18.31/18.51  thf('92', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i]:
% 18.31/18.51         (~ (r2_hidden @ (k3_tarski @ X0) @ (u1_pre_topc @ X1))
% 18.31/18.51          | (zip_tseitin_5 @ X0 @ X1)
% 18.31/18.51          | (zip_tseitin_4 @ X0 @ X1))),
% 18.31/18.51      inference('sup-', [status(thm)], ['90', '91'])).
% 18.31/18.51  thf('93', plain,
% 18.31/18.51      (![X48 : $i, X50 : $i]:
% 18.31/18.51         ((zip_tseitin_5 @ X48 @ X50) | ~ (zip_tseitin_4 @ X48 @ X50))),
% 18.31/18.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 18.31/18.51  thf('94', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i]:
% 18.31/18.51         ((zip_tseitin_5 @ X0 @ X1)
% 18.31/18.51          | ~ (r2_hidden @ (k3_tarski @ X0) @ (u1_pre_topc @ X1)))),
% 18.31/18.51      inference('clc', [status(thm)], ['92', '93'])).
% 18.31/18.51  thf('95', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i]:
% 18.31/18.51         (~ (r2_hidden @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X1))
% 18.31/18.51          | ~ (l1_pre_topc @ X0)
% 18.31/18.51          | ~ (v2_pre_topc @ X0)
% 18.31/18.51          | (zip_tseitin_5 @ (u1_pre_topc @ X0) @ X1))),
% 18.31/18.51      inference('sup-', [status(thm)], ['87', '94'])).
% 18.31/18.51  thf('96', plain,
% 18.31/18.51      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_pre_topc @ sk_A)))
% 18.31/18.51        | (zip_tseitin_5 @ (u1_pre_topc @ sk_A) @ sk_A)
% 18.31/18.51        | ~ (v2_pre_topc @ sk_A)
% 18.31/18.51        | ~ (l1_pre_topc @ sk_A))),
% 18.31/18.51      inference('sup-', [status(thm)], ['86', '95'])).
% 18.31/18.51  thf('97', plain, ((v2_pre_topc @ sk_A)),
% 18.31/18.51      inference('cnf', [status(esa)], [zf_stmt_13])).
% 18.31/18.51  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 18.31/18.51      inference('cnf', [status(esa)], [zf_stmt_13])).
% 18.31/18.51  thf('99', plain,
% 18.31/18.51      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_pre_topc @ sk_A)))
% 18.31/18.51        | (zip_tseitin_5 @ (u1_pre_topc @ sk_A) @ sk_A))),
% 18.31/18.51      inference('demod', [status(thm)], ['96', '97', '98'])).
% 18.31/18.51  thf('100', plain,
% 18.31/18.51      (![X14 : $i, X15 : $i]:
% 18.31/18.51         (~ (v1_xboole_0 @ X15)
% 18.31/18.51          | (m1_subset_1 @ X15 @ X14)
% 18.31/18.51          | ~ (v1_xboole_0 @ X14))),
% 18.31/18.51      inference('cnf', [status(esa)], [d2_subset_1])).
% 18.31/18.51  thf('101', plain,
% 18.31/18.51      (![X24 : $i, X25 : $i, X26 : $i]:
% 18.31/18.51         (~ (r2_hidden @ X24 @ X25)
% 18.31/18.51          | ~ (v1_xboole_0 @ X26)
% 18.31/18.51          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 18.31/18.51      inference('cnf', [status(esa)], [t5_subset])).
% 18.31/18.51  thf('102', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.31/18.51         (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 18.31/18.51          | ~ (v1_xboole_0 @ X1)
% 18.31/18.51          | ~ (v1_xboole_0 @ X0)
% 18.31/18.51          | ~ (r2_hidden @ X2 @ X1))),
% 18.31/18.51      inference('sup-', [status(thm)], ['100', '101'])).
% 18.31/18.51  thf('103', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i]:
% 18.31/18.51         ((zip_tseitin_5 @ (u1_pre_topc @ sk_A) @ sk_A)
% 18.31/18.51          | ~ (r2_hidden @ X1 @ X0)
% 18.31/18.51          | ~ (v1_xboole_0 @ (u1_pre_topc @ sk_A))
% 18.31/18.51          | ~ (v1_xboole_0 @ X0))),
% 18.31/18.51      inference('sup-', [status(thm)], ['99', '102'])).
% 18.31/18.51  thf('104', plain, ((v1_xboole_0 @ (u1_pre_topc @ sk_A))),
% 18.31/18.51      inference('simplify', [status(thm)], ['42'])).
% 18.31/18.51  thf('105', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i]:
% 18.31/18.51         ((zip_tseitin_5 @ (u1_pre_topc @ sk_A) @ sk_A)
% 18.31/18.51          | ~ (r2_hidden @ X1 @ X0)
% 18.31/18.51          | ~ (v1_xboole_0 @ X0))),
% 18.31/18.51      inference('demod', [status(thm)], ['103', '104'])).
% 18.31/18.51  thf('106', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (l1_pre_topc @ X0)
% 18.31/18.51          | ~ (v2_pre_topc @ X0)
% 18.31/18.51          | ~ (v1_xboole_0 @ (u1_pre_topc @ X0))
% 18.31/18.51          | (zip_tseitin_5 @ (u1_pre_topc @ sk_A) @ sk_A))),
% 18.31/18.51      inference('sup-', [status(thm)], ['44', '105'])).
% 18.31/18.51  thf('107', plain,
% 18.31/18.51      (((zip_tseitin_5 @ (u1_pre_topc @ sk_A) @ sk_A)
% 18.31/18.51        | ~ (v2_pre_topc @ sk_A)
% 18.31/18.51        | ~ (l1_pre_topc @ sk_A))),
% 18.31/18.51      inference('sup-', [status(thm)], ['43', '106'])).
% 18.31/18.51  thf('108', plain, ((v2_pre_topc @ sk_A)),
% 18.31/18.51      inference('cnf', [status(esa)], [zf_stmt_13])).
% 18.31/18.51  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 18.31/18.51      inference('cnf', [status(esa)], [zf_stmt_13])).
% 18.31/18.51  thf('110', plain, ((zip_tseitin_5 @ (u1_pre_topc @ sk_A) @ sk_A)),
% 18.31/18.51      inference('demod', [status(thm)], ['107', '108', '109'])).
% 18.31/18.51  thf('111', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (l1_pre_topc @ X0)
% 18.31/18.51          | ~ (zip_tseitin_5 @ (u1_pre_topc @ X0) @ X0)
% 18.31/18.51          | (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0))),
% 18.31/18.51      inference('sup-', [status(thm)], ['21', '22'])).
% 18.31/18.51  thf('112', plain,
% 18.31/18.51      (((zip_tseitin_4 @ (u1_pre_topc @ sk_A) @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 18.31/18.51      inference('sup-', [status(thm)], ['110', '111'])).
% 18.31/18.51  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 18.31/18.51      inference('cnf', [status(esa)], [zf_stmt_13])).
% 18.31/18.51  thf('114', plain, ((zip_tseitin_4 @ (u1_pre_topc @ sk_A) @ sk_A)),
% 18.31/18.51      inference('demod', [status(thm)], ['112', '113'])).
% 18.31/18.51  thf('115', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0)
% 18.31/18.51          | (r2_hidden @ 
% 18.31/18.51             (k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 18.31/18.51             (u1_pre_topc @ X0)))),
% 18.31/18.51      inference('sup-', [status(thm)], ['26', '27'])).
% 18.31/18.51  thf('116', plain,
% 18.31/18.51      ((r2_hidden @ 
% 18.31/18.51        (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 18.31/18.51        (u1_pre_topc @ sk_A))),
% 18.31/18.51      inference('sup-', [status(thm)], ['114', '115'])).
% 18.31/18.51  thf('117', plain,
% 18.31/18.51      (((r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 18.31/18.51        | ~ (l1_pre_topc @ sk_A)
% 18.31/18.51        | ~ (v2_pre_topc @ sk_A))),
% 18.31/18.51      inference('sup+', [status(thm)], ['12', '116'])).
% 18.31/18.51  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 18.31/18.51      inference('cnf', [status(esa)], [zf_stmt_13])).
% 18.31/18.51  thf('119', plain, ((v2_pre_topc @ sk_A)),
% 18.31/18.51      inference('cnf', [status(esa)], [zf_stmt_13])).
% 18.31/18.51  thf('120', plain,
% 18.31/18.51      ((r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))),
% 18.31/18.51      inference('demod', [status(thm)], ['117', '118', '119'])).
% 18.31/18.51  thf('121', plain, ((v1_xboole_0 @ (u1_pre_topc @ sk_A))),
% 18.31/18.51      inference('simplify', [status(thm)], ['42'])).
% 18.31/18.51  thf('122', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (v2_pre_topc @ X0)
% 18.31/18.51          | ~ (l1_pre_topc @ X0)
% 18.31/18.51          | ((k3_tarski @ (u1_pre_topc @ X0)) = (u1_struct_0 @ X0)))),
% 18.31/18.51      inference('simplify', [status(thm)], ['17'])).
% 18.31/18.51  thf('123', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (v2_pre_topc @ X0)
% 18.31/18.51          | ~ (l1_pre_topc @ X0)
% 18.31/18.51          | (r2_hidden @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_pre_topc @ X0)))),
% 18.31/18.51      inference('simplify', [status(thm)], ['30'])).
% 18.31/18.51  thf('124', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i]:
% 18.31/18.51         (~ (r2_hidden @ X1 @ X0)
% 18.31/18.51          | (r2_hidden @ X1 @ (sk_D_1 @ X1 @ (k1_zfmisc_1 @ X0))))),
% 18.31/18.51      inference('sup-', [status(thm)], ['78', '80'])).
% 18.31/18.51  thf('125', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (l1_pre_topc @ X0)
% 18.31/18.51          | ~ (v2_pre_topc @ X0)
% 18.31/18.51          | (r2_hidden @ (k3_tarski @ (u1_pre_topc @ X0)) @ 
% 18.31/18.51             (sk_D_1 @ (k3_tarski @ (u1_pre_topc @ X0)) @ 
% 18.31/18.51              (k1_zfmisc_1 @ (u1_pre_topc @ X0)))))),
% 18.31/18.51      inference('sup-', [status(thm)], ['123', '124'])).
% 18.31/18.51  thf('126', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         ((r2_hidden @ (k3_tarski @ (u1_pre_topc @ X0)) @ 
% 18.31/18.51           (sk_D_1 @ (u1_struct_0 @ X0) @ (k1_zfmisc_1 @ (u1_pre_topc @ X0))))
% 18.31/18.51          | ~ (l1_pre_topc @ X0)
% 18.31/18.51          | ~ (v2_pre_topc @ X0)
% 18.31/18.51          | ~ (v2_pre_topc @ X0)
% 18.31/18.51          | ~ (l1_pre_topc @ X0))),
% 18.31/18.51      inference('sup+', [status(thm)], ['122', '125'])).
% 18.31/18.51  thf('127', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (v2_pre_topc @ X0)
% 18.31/18.51          | ~ (l1_pre_topc @ X0)
% 18.31/18.51          | (r2_hidden @ (k3_tarski @ (u1_pre_topc @ X0)) @ 
% 18.31/18.51             (sk_D_1 @ (u1_struct_0 @ X0) @ (k1_zfmisc_1 @ (u1_pre_topc @ X0)))))),
% 18.31/18.51      inference('simplify', [status(thm)], ['126'])).
% 18.31/18.51  thf('128', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (l1_pre_topc @ X0)
% 18.31/18.51          | ~ (v2_pre_topc @ X0)
% 18.31/18.51          | (r2_hidden @ 
% 18.31/18.51             (sk_D_1 @ (u1_struct_0 @ X0) @ (k1_zfmisc_1 @ (u1_pre_topc @ X0))) @ 
% 18.31/18.51             (k1_zfmisc_1 @ (u1_pre_topc @ X0))))),
% 18.31/18.51      inference('sup-', [status(thm)], ['46', '50'])).
% 18.31/18.51  thf('129', plain,
% 18.31/18.51      (![X13 : $i, X14 : $i]:
% 18.31/18.51         (~ (r2_hidden @ X13 @ X14)
% 18.31/18.51          | (m1_subset_1 @ X13 @ X14)
% 18.31/18.51          | (v1_xboole_0 @ X14))),
% 18.31/18.51      inference('cnf', [status(esa)], [d2_subset_1])).
% 18.31/18.51  thf('130', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (v2_pre_topc @ X0)
% 18.31/18.51          | ~ (l1_pre_topc @ X0)
% 18.31/18.51          | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_pre_topc @ X0)))
% 18.31/18.51          | (m1_subset_1 @ 
% 18.31/18.51             (sk_D_1 @ (u1_struct_0 @ X0) @ (k1_zfmisc_1 @ (u1_pre_topc @ X0))) @ 
% 18.31/18.51             (k1_zfmisc_1 @ (u1_pre_topc @ X0))))),
% 18.31/18.51      inference('sup-', [status(thm)], ['128', '129'])).
% 18.31/18.51  thf('131', plain,
% 18.31/18.51      (![X24 : $i, X25 : $i, X26 : $i]:
% 18.31/18.51         (~ (r2_hidden @ X24 @ X25)
% 18.31/18.51          | ~ (v1_xboole_0 @ X26)
% 18.31/18.51          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 18.31/18.51      inference('cnf', [status(esa)], [t5_subset])).
% 18.31/18.51  thf('132', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i]:
% 18.31/18.51         ((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_pre_topc @ X0)))
% 18.31/18.51          | ~ (l1_pre_topc @ X0)
% 18.31/18.51          | ~ (v2_pre_topc @ X0)
% 18.31/18.51          | ~ (v1_xboole_0 @ (u1_pre_topc @ X0))
% 18.31/18.51          | ~ (r2_hidden @ X1 @ 
% 18.31/18.51               (sk_D_1 @ (u1_struct_0 @ X0) @ 
% 18.31/18.51                (k1_zfmisc_1 @ (u1_pre_topc @ X0)))))),
% 18.31/18.51      inference('sup-', [status(thm)], ['130', '131'])).
% 18.31/18.51  thf('133', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         (~ (l1_pre_topc @ X0)
% 18.31/18.51          | ~ (v2_pre_topc @ X0)
% 18.31/18.51          | ~ (v1_xboole_0 @ (u1_pre_topc @ X0))
% 18.31/18.51          | ~ (v2_pre_topc @ X0)
% 18.31/18.51          | ~ (l1_pre_topc @ X0)
% 18.31/18.51          | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_pre_topc @ X0))))),
% 18.31/18.51      inference('sup-', [status(thm)], ['127', '132'])).
% 18.31/18.51  thf('134', plain,
% 18.31/18.51      (![X0 : $i]:
% 18.31/18.51         ((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_pre_topc @ X0)))
% 18.31/18.51          | ~ (v1_xboole_0 @ (u1_pre_topc @ X0))
% 18.31/18.51          | ~ (v2_pre_topc @ X0)
% 18.31/18.51          | ~ (l1_pre_topc @ X0))),
% 18.31/18.51      inference('simplify', [status(thm)], ['133'])).
% 18.31/18.51  thf('135', plain,
% 18.31/18.51      ((~ (l1_pre_topc @ sk_A)
% 18.31/18.51        | ~ (v2_pre_topc @ sk_A)
% 18.31/18.51        | (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_pre_topc @ sk_A))))),
% 18.31/18.51      inference('sup-', [status(thm)], ['121', '134'])).
% 18.31/18.51  thf('136', plain, ((l1_pre_topc @ sk_A)),
% 18.31/18.51      inference('cnf', [status(esa)], [zf_stmt_13])).
% 18.31/18.51  thf('137', plain, ((v2_pre_topc @ sk_A)),
% 18.31/18.51      inference('cnf', [status(esa)], [zf_stmt_13])).
% 18.31/18.51  thf('138', plain, ((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_pre_topc @ sk_A)))),
% 18.31/18.51      inference('demod', [status(thm)], ['135', '136', '137'])).
% 18.31/18.51  thf('139', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.31/18.51         (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 18.31/18.51          | ~ (v1_xboole_0 @ X1)
% 18.31/18.51          | ~ (v1_xboole_0 @ X0)
% 18.31/18.51          | ~ (r2_hidden @ X2 @ X1))),
% 18.31/18.51      inference('sup-', [status(thm)], ['100', '101'])).
% 18.31/18.51  thf('140', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i]:
% 18.31/18.51         (~ (r2_hidden @ X1 @ X0)
% 18.31/18.51          | ~ (v1_xboole_0 @ (u1_pre_topc @ sk_A))
% 18.31/18.51          | ~ (v1_xboole_0 @ X0))),
% 18.31/18.51      inference('sup-', [status(thm)], ['138', '139'])).
% 18.31/18.51  thf('141', plain, ((v1_xboole_0 @ (u1_pre_topc @ sk_A))),
% 18.31/18.51      inference('simplify', [status(thm)], ['42'])).
% 18.31/18.51  thf('142', plain,
% 18.31/18.51      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 18.31/18.51      inference('demod', [status(thm)], ['140', '141'])).
% 18.31/18.51  thf('143', plain, (~ (v1_xboole_0 @ (u1_pre_topc @ sk_A))),
% 18.31/18.51      inference('sup-', [status(thm)], ['120', '142'])).
% 18.31/18.51  thf('144', plain, ((v1_xboole_0 @ (u1_pre_topc @ sk_A))),
% 18.31/18.51      inference('simplify', [status(thm)], ['42'])).
% 18.31/18.51  thf('145', plain, ($false), inference('demod', [status(thm)], ['143', '144'])).
% 18.31/18.51  
% 18.31/18.51  % SZS output end Refutation
% 18.31/18.51  
% 18.31/18.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
