%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1riLGirUg5

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:22 EST 2020

% Result     : Theorem 12.27s
% Output     : Refutation 12.27s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 372 expanded)
%              Number of leaves         :   48 ( 134 expanded)
%              Depth                    :   24
%              Number of atoms          : 1361 (3060 expanded)
%              Number of equality atoms :   27 (  82 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X51: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X51 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(redefinition_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k5_setfam_1 @ A @ B )
        = ( k3_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k5_setfam_1 @ X19 @ X18 )
        = ( k3_tarski @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t24_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) )
        = ( u1_struct_0 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) )
          = ( u1_struct_0 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_yellow_1])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf(zf_stmt_1,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_5 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
       => ( zip_tseitin_4 @ B @ A ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_4 @ B @ A )
    <=> ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) )
       => ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_3 @ B @ A )
    <=> ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ! [C: $i] :
            ( zip_tseitin_2 @ C @ B @ A ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
    <=> ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
       => ( zip_tseitin_1 @ C @ B @ A ) ) ) )).

thf(zf_stmt_9,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
    <=> ( ( zip_tseitin_0 @ C @ B @ A )
       => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_11,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_12,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
    <=> ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
        & ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ) )).

thf(zf_stmt_13,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ A )
      <=> ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
          & ! [B: $i] :
              ( zip_tseitin_5 @ B @ A )
          & ! [B: $i] :
              ( zip_tseitin_3 @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X48: $i,X50: $i] :
      ( ~ ( v2_pre_topc @ X48 )
      | ( zip_tseitin_5 @ X50 @ X48 )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X42: $i,X44: $i] :
      ( ( zip_tseitin_4 @ X42 @ X44 )
      | ( r1_tarski @ X42 @ ( u1_pre_topc @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_4 @ X1 @ X0 )
      | ( r2_hidden @ X2 @ ( u1_pre_topc @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( u1_pre_topc @ X2 ) )
      | ( zip_tseitin_4 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X51: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X51 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_4 @ X1 @ X0 )
      | ( r1_tarski @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( zip_tseitin_4 @ X1 @ X0 )
      | ( r1_tarski @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_4 @ X1 @ X0 )
      | ( r1_tarski @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( zip_tseitin_4 @ X1 @ X0 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) ) )
      | ( zip_tseitin_4 @ X45 @ X46 )
      | ~ ( zip_tseitin_5 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_4 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( zip_tseitin_5 @ X1 @ X0 )
      | ( zip_tseitin_4 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_5 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( zip_tseitin_4 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( zip_tseitin_4 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_4 @ X1 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ( zip_tseitin_4 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( zip_tseitin_4 @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( r1_tarski @ X42 @ ( u1_pre_topc @ X43 ) )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X43 ) @ X42 ) @ ( u1_pre_topc @ X43 ) )
      | ~ ( zip_tseitin_4 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,
    ( ( r2_hidden @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['2','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    r2_hidden @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('38',plain,
    ( ( r2_hidden @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r2_hidden @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('41',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( m1_subset_1 @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( m1_subset_1 @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('45',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('47',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ~ ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k5_setfam_1 @ X19 @ X18 )
        = ( k3_tarski @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k5_setfam_1 @ X0 @ X1 )
        = ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('55',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r2_hidden @ ( sk_D_1 @ X11 @ X8 ) @ X8 )
      | ( X10
       != ( k3_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('56',plain,(
    ! [X8: $i,X11: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X11 @ X8 ) @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k3_tarski @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k3_tarski @ X0 ) ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X0 ) @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('61',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_tarski @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_setfam_1 @ X1 @ X0 )
        = X2 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k5_setfam_1 @ X1 @ X0 )
        = X2 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X48: $i,X50: $i] :
      ( ~ ( v2_pre_topc @ X48 )
      | ( zip_tseitin_5 @ X50 @ X48 )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('69',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) ) )
      | ( zip_tseitin_4 @ X45 @ X46 )
      | ~ ( zip_tseitin_5 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( zip_tseitin_5 @ X1 @ X0 )
      | ( zip_tseitin_4 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( zip_tseitin_4 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_4 @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_4 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('76',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( r1_tarski @ X42 @ ( u1_pre_topc @ X43 ) )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X43 ) @ X42 ) @ ( u1_pre_topc @ X43 ) )
      | ~ ( zip_tseitin_4 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( zip_tseitin_4 @ X1 @ X0 )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ X1 ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_A ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(condensation,[status(thm)],['88'])).

thf('90',plain,(
    m1_subset_1 @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['42','89'])).

thf('91',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('92',plain,(
    r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('94',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('96',plain,(
    ! [X48: $i,X50: $i] :
      ( ~ ( v2_pre_topc @ X48 )
      | ( zip_tseitin_5 @ X50 @ X48 )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('97',plain,(
    ! [X51: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X51 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('98',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) ) )
      | ( zip_tseitin_4 @ X45 @ X46 )
      | ~ ( zip_tseitin_5 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( zip_tseitin_5 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['95','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('106',plain,(
    ! [X52: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X52 ) @ X52 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X52 ) )
        = ( k3_tarski @ X52 ) )
      | ( v1_xboole_0 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('108',plain,(
    ! [X52: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ X52 ) )
        = ( k3_tarski @ X52 ) )
      | ~ ( r2_hidden @ ( k3_tarski @ X52 ) @ X52 ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('110',plain,(
    ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,(
    ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['94','114'])).

thf('116',plain,(
    r2_hidden @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('117',plain,(
    ! [X48: $i] :
      ( ~ ( v2_pre_topc @ X48 )
      | ( r2_hidden @ ( u1_struct_0 @ X48 ) @ ( u1_pre_topc @ X48 ) )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('118',plain,(
    ! [X26: $i,X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X26 @ X29 )
      | ~ ( r2_hidden @ X28 @ ( u1_pre_topc @ X29 ) )
      | ~ ( r2_hidden @ X26 @ ( u1_pre_topc @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ X0 ) @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,
    ( ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['116','119'])).

thf('121',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ X28 @ ( u1_pre_topc @ X27 ) )
      | ~ ( zip_tseitin_0 @ X28 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('125',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('127',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ( r2_hidden @ X9 @ X10 )
      | ( X10
       != ( k3_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('128',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X9 @ ( k3_tarski @ X8 ) )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['126','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) )
      | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','129'])).

thf('131',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('132',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) )
    | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    $false ),
    inference(demod,[status(thm)],['115','133'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1riLGirUg5
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:05:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 12.27/12.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 12.27/12.53  % Solved by: fo/fo7.sh
% 12.27/12.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.27/12.53  % done 6603 iterations in 12.036s
% 12.27/12.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 12.27/12.53  % SZS output start Refutation
% 12.27/12.53  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 12.27/12.53  thf(sk_A_type, type, sk_A: $i).
% 12.27/12.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 12.27/12.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 12.27/12.53  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 12.27/12.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 12.27/12.53  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 12.27/12.53  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 12.27/12.53  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 12.27/12.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 12.27/12.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 12.27/12.53  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 12.27/12.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 12.27/12.53  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 12.27/12.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 12.27/12.53  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 12.27/12.53  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 12.27/12.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 12.27/12.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 12.27/12.53  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 12.27/12.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 12.27/12.53  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 12.27/12.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 12.27/12.53  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 12.27/12.53  thf(dt_u1_pre_topc, axiom,
% 12.27/12.53    (![A:$i]:
% 12.27/12.53     ( ( l1_pre_topc @ A ) =>
% 12.27/12.53       ( m1_subset_1 @
% 12.27/12.53         ( u1_pre_topc @ A ) @ 
% 12.27/12.53         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 12.27/12.53  thf('0', plain,
% 12.27/12.53      (![X51 : $i]:
% 12.27/12.53         ((m1_subset_1 @ (u1_pre_topc @ X51) @ 
% 12.27/12.53           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51))))
% 12.27/12.53          | ~ (l1_pre_topc @ X51))),
% 12.27/12.53      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 12.27/12.53  thf(redefinition_k5_setfam_1, axiom,
% 12.27/12.53    (![A:$i,B:$i]:
% 12.27/12.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 12.27/12.53       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 12.27/12.53  thf('1', plain,
% 12.27/12.53      (![X18 : $i, X19 : $i]:
% 12.27/12.53         (((k5_setfam_1 @ X19 @ X18) = (k3_tarski @ X18))
% 12.27/12.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 12.27/12.53      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 12.27/12.53  thf('2', plain,
% 12.27/12.53      (![X0 : $i]:
% 12.27/12.53         (~ (l1_pre_topc @ X0)
% 12.27/12.53          | ((k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 12.27/12.53              = (k3_tarski @ (u1_pre_topc @ X0))))),
% 12.27/12.53      inference('sup-', [status(thm)], ['0', '1'])).
% 12.27/12.53  thf(t24_yellow_1, conjecture,
% 12.27/12.53    (![A:$i]:
% 12.27/12.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 12.27/12.53       ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 12.27/12.53         ( u1_struct_0 @ A ) ) ))).
% 12.27/12.53  thf(zf_stmt_0, negated_conjecture,
% 12.27/12.53    (~( ![A:$i]:
% 12.27/12.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 12.27/12.53            ( l1_pre_topc @ A ) ) =>
% 12.27/12.53          ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 12.27/12.53            ( u1_struct_0 @ A ) ) ) )),
% 12.27/12.53    inference('cnf.neg', [status(esa)], [t24_yellow_1])).
% 12.27/12.53  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 12.27/12.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.27/12.53  thf(d1_pre_topc, axiom,
% 12.27/12.53    (![A:$i]:
% 12.27/12.53     ( ( l1_pre_topc @ A ) =>
% 12.27/12.53       ( ( v2_pre_topc @ A ) <=>
% 12.27/12.53         ( ( ![B:$i]:
% 12.27/12.53             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.27/12.53               ( ![C:$i]:
% 12.27/12.53                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.27/12.53                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 12.27/12.53                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 12.27/12.53                     ( r2_hidden @
% 12.27/12.53                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 12.27/12.53                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 12.27/12.53           ( ![B:$i]:
% 12.27/12.53             ( ( m1_subset_1 @
% 12.27/12.53                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 12.27/12.53               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 12.27/12.53                 ( r2_hidden @
% 12.27/12.53                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 12.27/12.53                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 12.27/12.53           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 12.27/12.53  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $o).
% 12.27/12.53  thf(zf_stmt_2, axiom,
% 12.27/12.53    (![B:$i,A:$i]:
% 12.27/12.53     ( ( zip_tseitin_5 @ B @ A ) <=>
% 12.27/12.53       ( ( m1_subset_1 @
% 12.27/12.53           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 12.27/12.53         ( zip_tseitin_4 @ B @ A ) ) ))).
% 12.27/12.53  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 12.27/12.53  thf(zf_stmt_4, axiom,
% 12.27/12.53    (![B:$i,A:$i]:
% 12.27/12.53     ( ( zip_tseitin_4 @ B @ A ) <=>
% 12.27/12.53       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 12.27/12.53         ( r2_hidden @
% 12.27/12.53           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 12.27/12.53  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 12.27/12.53  thf(zf_stmt_6, axiom,
% 12.27/12.53    (![B:$i,A:$i]:
% 12.27/12.53     ( ( zip_tseitin_3 @ B @ A ) <=>
% 12.27/12.53       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.27/12.53         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 12.27/12.53  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 12.27/12.53  thf(zf_stmt_8, axiom,
% 12.27/12.53    (![C:$i,B:$i,A:$i]:
% 12.27/12.53     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 12.27/12.53       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 12.27/12.53         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 12.27/12.53  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 12.27/12.53  thf(zf_stmt_10, axiom,
% 12.27/12.53    (![C:$i,B:$i,A:$i]:
% 12.27/12.53     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 12.27/12.53       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 12.27/12.53         ( r2_hidden @
% 12.27/12.53           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 12.27/12.53  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 12.27/12.53  thf(zf_stmt_12, axiom,
% 12.27/12.53    (![C:$i,B:$i,A:$i]:
% 12.27/12.53     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 12.27/12.53       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 12.27/12.53         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 12.27/12.53  thf(zf_stmt_13, axiom,
% 12.27/12.53    (![A:$i]:
% 12.27/12.53     ( ( l1_pre_topc @ A ) =>
% 12.27/12.53       ( ( v2_pre_topc @ A ) <=>
% 12.27/12.53         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 12.27/12.53           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 12.27/12.53           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 12.27/12.53  thf('4', plain,
% 12.27/12.53      (![X48 : $i, X50 : $i]:
% 12.27/12.53         (~ (v2_pre_topc @ X48)
% 12.27/12.53          | (zip_tseitin_5 @ X50 @ X48)
% 12.27/12.53          | ~ (l1_pre_topc @ X48))),
% 12.27/12.53      inference('cnf', [status(esa)], [zf_stmt_13])).
% 12.27/12.53  thf(d3_tarski, axiom,
% 12.27/12.53    (![A:$i,B:$i]:
% 12.27/12.53     ( ( r1_tarski @ A @ B ) <=>
% 12.27/12.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 12.27/12.53  thf('5', plain,
% 12.27/12.53      (![X1 : $i, X3 : $i]:
% 12.27/12.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 12.27/12.53      inference('cnf', [status(esa)], [d3_tarski])).
% 12.27/12.53  thf('6', plain,
% 12.27/12.53      (![X42 : $i, X44 : $i]:
% 12.27/12.53         ((zip_tseitin_4 @ X42 @ X44) | (r1_tarski @ X42 @ (u1_pre_topc @ X44)))),
% 12.27/12.53      inference('cnf', [status(esa)], [zf_stmt_4])).
% 12.27/12.53  thf('7', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.27/12.53         (~ (r2_hidden @ X0 @ X1)
% 12.27/12.53          | (r2_hidden @ X0 @ X2)
% 12.27/12.53          | ~ (r1_tarski @ X1 @ X2))),
% 12.27/12.53      inference('cnf', [status(esa)], [d3_tarski])).
% 12.27/12.53  thf('8', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.27/12.53         ((zip_tseitin_4 @ X1 @ X0)
% 12.27/12.53          | (r2_hidden @ X2 @ (u1_pre_topc @ X0))
% 12.27/12.53          | ~ (r2_hidden @ X2 @ X1))),
% 12.27/12.53      inference('sup-', [status(thm)], ['6', '7'])).
% 12.27/12.53  thf('9', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.27/12.53         ((r1_tarski @ X0 @ X1)
% 12.27/12.53          | (r2_hidden @ (sk_C @ X1 @ X0) @ (u1_pre_topc @ X2))
% 12.27/12.53          | (zip_tseitin_4 @ X0 @ X2))),
% 12.27/12.53      inference('sup-', [status(thm)], ['5', '8'])).
% 12.27/12.53  thf('10', plain,
% 12.27/12.53      (![X51 : $i]:
% 12.27/12.53         ((m1_subset_1 @ (u1_pre_topc @ X51) @ 
% 12.27/12.53           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51))))
% 12.27/12.53          | ~ (l1_pre_topc @ X51))),
% 12.27/12.53      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 12.27/12.53  thf(t3_subset, axiom,
% 12.27/12.53    (![A:$i,B:$i]:
% 12.27/12.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 12.27/12.53  thf('11', plain,
% 12.27/12.53      (![X20 : $i, X21 : $i]:
% 12.27/12.53         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 12.27/12.53      inference('cnf', [status(esa)], [t3_subset])).
% 12.27/12.53  thf('12', plain,
% 12.27/12.53      (![X0 : $i]:
% 12.27/12.53         (~ (l1_pre_topc @ X0)
% 12.27/12.53          | (r1_tarski @ (u1_pre_topc @ X0) @ 
% 12.27/12.53             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 12.27/12.53      inference('sup-', [status(thm)], ['10', '11'])).
% 12.27/12.53  thf('13', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.27/12.53         (~ (r2_hidden @ X0 @ X1)
% 12.27/12.53          | (r2_hidden @ X0 @ X2)
% 12.27/12.53          | ~ (r1_tarski @ X1 @ X2))),
% 12.27/12.53      inference('cnf', [status(esa)], [d3_tarski])).
% 12.27/12.53  thf('14', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]:
% 12.27/12.53         (~ (l1_pre_topc @ X0)
% 12.27/12.53          | (r2_hidden @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 12.27/12.53          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0)))),
% 12.27/12.53      inference('sup-', [status(thm)], ['12', '13'])).
% 12.27/12.53  thf('15', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.27/12.53         ((zip_tseitin_4 @ X1 @ X0)
% 12.27/12.53          | (r1_tarski @ X1 @ X2)
% 12.27/12.53          | (r2_hidden @ (sk_C @ X2 @ X1) @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 12.27/12.53          | ~ (l1_pre_topc @ X0))),
% 12.27/12.53      inference('sup-', [status(thm)], ['9', '14'])).
% 12.27/12.53  thf('16', plain,
% 12.27/12.53      (![X1 : $i, X3 : $i]:
% 12.27/12.53         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 12.27/12.53      inference('cnf', [status(esa)], [d3_tarski])).
% 12.27/12.53  thf('17', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]:
% 12.27/12.53         (~ (l1_pre_topc @ X0)
% 12.27/12.53          | (r1_tarski @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 12.27/12.53          | (zip_tseitin_4 @ X1 @ X0)
% 12.27/12.53          | (r1_tarski @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 12.27/12.53      inference('sup-', [status(thm)], ['15', '16'])).
% 12.27/12.53  thf('18', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]:
% 12.27/12.53         ((zip_tseitin_4 @ X1 @ X0)
% 12.27/12.53          | (r1_tarski @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 12.27/12.53          | ~ (l1_pre_topc @ X0))),
% 12.27/12.53      inference('simplify', [status(thm)], ['17'])).
% 12.27/12.53  thf('19', plain,
% 12.27/12.53      (![X20 : $i, X22 : $i]:
% 12.27/12.53         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 12.27/12.53      inference('cnf', [status(esa)], [t3_subset])).
% 12.27/12.53  thf('20', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]:
% 12.27/12.53         (~ (l1_pre_topc @ X0)
% 12.27/12.53          | (zip_tseitin_4 @ X1 @ X0)
% 12.27/12.53          | (m1_subset_1 @ X1 @ 
% 12.27/12.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))),
% 12.27/12.53      inference('sup-', [status(thm)], ['18', '19'])).
% 12.27/12.53  thf('21', plain,
% 12.27/12.53      (![X45 : $i, X46 : $i]:
% 12.27/12.53         (~ (m1_subset_1 @ X45 @ 
% 12.27/12.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46))))
% 12.27/12.53          | (zip_tseitin_4 @ X45 @ X46)
% 12.27/12.53          | ~ (zip_tseitin_5 @ X45 @ X46))),
% 12.27/12.53      inference('cnf', [status(esa)], [zf_stmt_2])).
% 12.27/12.53  thf('22', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]:
% 12.27/12.53         ((zip_tseitin_4 @ X1 @ X0)
% 12.27/12.53          | ~ (l1_pre_topc @ X0)
% 12.27/12.53          | ~ (zip_tseitin_5 @ X1 @ X0)
% 12.27/12.53          | (zip_tseitin_4 @ X1 @ X0))),
% 12.27/12.53      inference('sup-', [status(thm)], ['20', '21'])).
% 12.27/12.53  thf('23', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]:
% 12.27/12.53         (~ (zip_tseitin_5 @ X1 @ X0)
% 12.27/12.53          | ~ (l1_pre_topc @ X0)
% 12.27/12.53          | (zip_tseitin_4 @ X1 @ X0))),
% 12.27/12.53      inference('simplify', [status(thm)], ['22'])).
% 12.27/12.53  thf('24', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]:
% 12.27/12.53         (~ (l1_pre_topc @ X0)
% 12.27/12.53          | ~ (v2_pre_topc @ X0)
% 12.27/12.53          | (zip_tseitin_4 @ X1 @ X0)
% 12.27/12.53          | ~ (l1_pre_topc @ X0))),
% 12.27/12.53      inference('sup-', [status(thm)], ['4', '23'])).
% 12.27/12.53  thf('25', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]:
% 12.27/12.53         ((zip_tseitin_4 @ X1 @ X0)
% 12.27/12.53          | ~ (v2_pre_topc @ X0)
% 12.27/12.53          | ~ (l1_pre_topc @ X0))),
% 12.27/12.53      inference('simplify', [status(thm)], ['24'])).
% 12.27/12.53  thf('26', plain,
% 12.27/12.53      (![X0 : $i]: (~ (v2_pre_topc @ sk_A) | (zip_tseitin_4 @ X0 @ sk_A))),
% 12.27/12.53      inference('sup-', [status(thm)], ['3', '25'])).
% 12.27/12.53  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 12.27/12.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.27/12.53  thf('28', plain, (![X0 : $i]: (zip_tseitin_4 @ X0 @ sk_A)),
% 12.27/12.53      inference('demod', [status(thm)], ['26', '27'])).
% 12.27/12.53  thf(d10_xboole_0, axiom,
% 12.27/12.53    (![A:$i,B:$i]:
% 12.27/12.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 12.27/12.53  thf('29', plain,
% 12.27/12.53      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 12.27/12.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 12.27/12.53  thf('30', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 12.27/12.53      inference('simplify', [status(thm)], ['29'])).
% 12.27/12.53  thf('31', plain,
% 12.27/12.53      (![X42 : $i, X43 : $i]:
% 12.27/12.53         (~ (r1_tarski @ X42 @ (u1_pre_topc @ X43))
% 12.27/12.53          | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ X43) @ X42) @ 
% 12.27/12.53             (u1_pre_topc @ X43))
% 12.27/12.53          | ~ (zip_tseitin_4 @ X42 @ X43))),
% 12.27/12.53      inference('cnf', [status(esa)], [zf_stmt_4])).
% 12.27/12.53  thf('32', plain,
% 12.27/12.53      (![X0 : $i]:
% 12.27/12.53         (~ (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0)
% 12.27/12.53          | (r2_hidden @ 
% 12.27/12.53             (k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 12.27/12.53             (u1_pre_topc @ X0)))),
% 12.27/12.53      inference('sup-', [status(thm)], ['30', '31'])).
% 12.27/12.53  thf('33', plain,
% 12.27/12.53      ((r2_hidden @ 
% 12.27/12.53        (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 12.27/12.53        (u1_pre_topc @ sk_A))),
% 12.27/12.53      inference('sup-', [status(thm)], ['28', '32'])).
% 12.27/12.53  thf('34', plain,
% 12.27/12.53      (((r2_hidden @ (k3_tarski @ (u1_pre_topc @ sk_A)) @ (u1_pre_topc @ sk_A))
% 12.27/12.53        | ~ (l1_pre_topc @ sk_A))),
% 12.27/12.53      inference('sup+', [status(thm)], ['2', '33'])).
% 12.27/12.53  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 12.27/12.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.27/12.53  thf('36', plain,
% 12.27/12.53      ((r2_hidden @ (k3_tarski @ (u1_pre_topc @ sk_A)) @ (u1_pre_topc @ sk_A))),
% 12.27/12.53      inference('demod', [status(thm)], ['34', '35'])).
% 12.27/12.53  thf('37', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]:
% 12.27/12.53         (~ (l1_pre_topc @ X0)
% 12.27/12.53          | (r2_hidden @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 12.27/12.53          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0)))),
% 12.27/12.53      inference('sup-', [status(thm)], ['12', '13'])).
% 12.27/12.53  thf('38', plain,
% 12.27/12.53      (((r2_hidden @ (k3_tarski @ (u1_pre_topc @ sk_A)) @ 
% 12.27/12.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.27/12.53        | ~ (l1_pre_topc @ sk_A))),
% 12.27/12.53      inference('sup-', [status(thm)], ['36', '37'])).
% 12.27/12.53  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 12.27/12.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.27/12.53  thf('40', plain,
% 12.27/12.53      ((r2_hidden @ (k3_tarski @ (u1_pre_topc @ sk_A)) @ 
% 12.27/12.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.27/12.53      inference('demod', [status(thm)], ['38', '39'])).
% 12.27/12.53  thf(d2_subset_1, axiom,
% 12.27/12.53    (![A:$i,B:$i]:
% 12.27/12.53     ( ( ( v1_xboole_0 @ A ) =>
% 12.27/12.53         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 12.27/12.53       ( ( ~( v1_xboole_0 @ A ) ) =>
% 12.27/12.53         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 12.27/12.53  thf('41', plain,
% 12.27/12.53      (![X15 : $i, X16 : $i]:
% 12.27/12.53         (~ (r2_hidden @ X15 @ X16)
% 12.27/12.53          | (m1_subset_1 @ X15 @ X16)
% 12.27/12.53          | (v1_xboole_0 @ X16))),
% 12.27/12.53      inference('cnf', [status(esa)], [d2_subset_1])).
% 12.27/12.53  thf('42', plain,
% 12.27/12.53      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.27/12.53        | (m1_subset_1 @ (k3_tarski @ (u1_pre_topc @ sk_A)) @ 
% 12.27/12.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 12.27/12.53      inference('sup-', [status(thm)], ['40', '41'])).
% 12.27/12.53  thf('43', plain,
% 12.27/12.53      (![X1 : $i, X3 : $i]:
% 12.27/12.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 12.27/12.53      inference('cnf', [status(esa)], [d3_tarski])).
% 12.27/12.53  thf('44', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 12.27/12.53      inference('simplify', [status(thm)], ['29'])).
% 12.27/12.53  thf('45', plain,
% 12.27/12.53      (![X20 : $i, X22 : $i]:
% 12.27/12.53         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 12.27/12.53      inference('cnf', [status(esa)], [t3_subset])).
% 12.27/12.53  thf('46', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 12.27/12.53      inference('sup-', [status(thm)], ['44', '45'])).
% 12.27/12.53  thf(t5_subset, axiom,
% 12.27/12.53    (![A:$i,B:$i,C:$i]:
% 12.27/12.53     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 12.27/12.53          ( v1_xboole_0 @ C ) ) ))).
% 12.27/12.53  thf('47', plain,
% 12.27/12.53      (![X23 : $i, X24 : $i, X25 : $i]:
% 12.27/12.53         (~ (r2_hidden @ X23 @ X24)
% 12.27/12.53          | ~ (v1_xboole_0 @ X25)
% 12.27/12.53          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25)))),
% 12.27/12.53      inference('cnf', [status(esa)], [t5_subset])).
% 12.27/12.53  thf('48', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 12.27/12.53      inference('sup-', [status(thm)], ['46', '47'])).
% 12.27/12.53  thf('49', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 12.27/12.53      inference('sup-', [status(thm)], ['43', '48'])).
% 12.27/12.53  thf('50', plain,
% 12.27/12.53      (![X20 : $i, X22 : $i]:
% 12.27/12.53         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 12.27/12.53      inference('cnf', [status(esa)], [t3_subset])).
% 12.27/12.53  thf('51', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]:
% 12.27/12.53         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 12.27/12.53      inference('sup-', [status(thm)], ['49', '50'])).
% 12.27/12.53  thf('52', plain,
% 12.27/12.53      (![X18 : $i, X19 : $i]:
% 12.27/12.53         (((k5_setfam_1 @ X19 @ X18) = (k3_tarski @ X18))
% 12.27/12.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 12.27/12.53      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 12.27/12.53  thf('53', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]:
% 12.27/12.53         (~ (v1_xboole_0 @ X1) | ((k5_setfam_1 @ X0 @ X1) = (k3_tarski @ X1)))),
% 12.27/12.53      inference('sup-', [status(thm)], ['51', '52'])).
% 12.27/12.53  thf('54', plain,
% 12.27/12.53      (![X1 : $i, X3 : $i]:
% 12.27/12.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 12.27/12.53      inference('cnf', [status(esa)], [d3_tarski])).
% 12.27/12.53  thf(d4_tarski, axiom,
% 12.27/12.53    (![A:$i,B:$i]:
% 12.27/12.53     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 12.27/12.53       ( ![C:$i]:
% 12.27/12.53         ( ( r2_hidden @ C @ B ) <=>
% 12.27/12.53           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 12.27/12.53  thf('55', plain,
% 12.27/12.53      (![X8 : $i, X10 : $i, X11 : $i]:
% 12.27/12.53         (~ (r2_hidden @ X11 @ X10)
% 12.27/12.53          | (r2_hidden @ (sk_D_1 @ X11 @ X8) @ X8)
% 12.27/12.53          | ((X10) != (k3_tarski @ X8)))),
% 12.27/12.53      inference('cnf', [status(esa)], [d4_tarski])).
% 12.27/12.53  thf('56', plain,
% 12.27/12.53      (![X8 : $i, X11 : $i]:
% 12.27/12.53         ((r2_hidden @ (sk_D_1 @ X11 @ X8) @ X8)
% 12.27/12.53          | ~ (r2_hidden @ X11 @ (k3_tarski @ X8)))),
% 12.27/12.53      inference('simplify', [status(thm)], ['55'])).
% 12.27/12.53  thf('57', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]:
% 12.27/12.53         ((r1_tarski @ (k3_tarski @ X0) @ X1)
% 12.27/12.53          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k3_tarski @ X0)) @ X0) @ X0))),
% 12.27/12.53      inference('sup-', [status(thm)], ['54', '56'])).
% 12.27/12.53  thf('58', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 12.27/12.53      inference('sup-', [status(thm)], ['46', '47'])).
% 12.27/12.53  thf('59', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]:
% 12.27/12.53         ((r1_tarski @ (k3_tarski @ X0) @ X1) | ~ (v1_xboole_0 @ X0))),
% 12.27/12.53      inference('sup-', [status(thm)], ['57', '58'])).
% 12.27/12.53  thf('60', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 12.27/12.53      inference('sup-', [status(thm)], ['43', '48'])).
% 12.27/12.53  thf('61', plain,
% 12.27/12.53      (![X4 : $i, X6 : $i]:
% 12.27/12.53         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 12.27/12.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 12.27/12.53  thf('62', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]:
% 12.27/12.53         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 12.27/12.53      inference('sup-', [status(thm)], ['60', '61'])).
% 12.27/12.53  thf('63', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]:
% 12.27/12.53         (~ (v1_xboole_0 @ X1)
% 12.27/12.53          | ((k3_tarski @ X1) = (X0))
% 12.27/12.53          | ~ (v1_xboole_0 @ X0))),
% 12.27/12.53      inference('sup-', [status(thm)], ['59', '62'])).
% 12.27/12.53  thf('64', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.27/12.53         (((k5_setfam_1 @ X1 @ X0) = (X2))
% 12.27/12.53          | ~ (v1_xboole_0 @ X0)
% 12.27/12.53          | ~ (v1_xboole_0 @ X2)
% 12.27/12.53          | ~ (v1_xboole_0 @ X0))),
% 12.27/12.53      inference('sup+', [status(thm)], ['53', '63'])).
% 12.27/12.53  thf('65', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.27/12.53         (~ (v1_xboole_0 @ X2)
% 12.27/12.53          | ~ (v1_xboole_0 @ X0)
% 12.27/12.53          | ((k5_setfam_1 @ X1 @ X0) = (X2)))),
% 12.27/12.53      inference('simplify', [status(thm)], ['64'])).
% 12.27/12.53  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 12.27/12.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.27/12.53  thf('67', plain,
% 12.27/12.53      (![X48 : $i, X50 : $i]:
% 12.27/12.53         (~ (v2_pre_topc @ X48)
% 12.27/12.53          | (zip_tseitin_5 @ X50 @ X48)
% 12.27/12.53          | ~ (l1_pre_topc @ X48))),
% 12.27/12.53      inference('cnf', [status(esa)], [zf_stmt_13])).
% 12.27/12.53  thf('68', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]:
% 12.27/12.53         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 12.27/12.53      inference('sup-', [status(thm)], ['49', '50'])).
% 12.27/12.53  thf('69', plain,
% 12.27/12.53      (![X45 : $i, X46 : $i]:
% 12.27/12.53         (~ (m1_subset_1 @ X45 @ 
% 12.27/12.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46))))
% 12.27/12.53          | (zip_tseitin_4 @ X45 @ X46)
% 12.27/12.53          | ~ (zip_tseitin_5 @ X45 @ X46))),
% 12.27/12.53      inference('cnf', [status(esa)], [zf_stmt_2])).
% 12.27/12.53  thf('70', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]:
% 12.27/12.53         (~ (v1_xboole_0 @ X1)
% 12.27/12.53          | ~ (zip_tseitin_5 @ X1 @ X0)
% 12.27/12.53          | (zip_tseitin_4 @ X1 @ X0))),
% 12.27/12.53      inference('sup-', [status(thm)], ['68', '69'])).
% 12.27/12.53  thf('71', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]:
% 12.27/12.53         (~ (l1_pre_topc @ X0)
% 12.27/12.53          | ~ (v2_pre_topc @ X0)
% 12.27/12.53          | (zip_tseitin_4 @ X1 @ X0)
% 12.27/12.53          | ~ (v1_xboole_0 @ X1))),
% 12.27/12.53      inference('sup-', [status(thm)], ['67', '70'])).
% 12.27/12.53  thf('72', plain,
% 12.27/12.53      (![X0 : $i]:
% 12.27/12.53         (~ (v1_xboole_0 @ X0)
% 12.27/12.53          | (zip_tseitin_4 @ X0 @ sk_A)
% 12.27/12.53          | ~ (v2_pre_topc @ sk_A))),
% 12.27/12.53      inference('sup-', [status(thm)], ['66', '71'])).
% 12.27/12.53  thf('73', plain, ((v2_pre_topc @ sk_A)),
% 12.27/12.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.27/12.53  thf('74', plain,
% 12.27/12.53      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (zip_tseitin_4 @ X0 @ sk_A))),
% 12.27/12.53      inference('demod', [status(thm)], ['72', '73'])).
% 12.27/12.53  thf('75', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 12.27/12.53      inference('sup-', [status(thm)], ['43', '48'])).
% 12.27/12.53  thf('76', plain,
% 12.27/12.53      (![X42 : $i, X43 : $i]:
% 12.27/12.53         (~ (r1_tarski @ X42 @ (u1_pre_topc @ X43))
% 12.27/12.53          | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ X43) @ X42) @ 
% 12.27/12.53             (u1_pre_topc @ X43))
% 12.27/12.53          | ~ (zip_tseitin_4 @ X42 @ X43))),
% 12.27/12.53      inference('cnf', [status(esa)], [zf_stmt_4])).
% 12.27/12.53  thf('77', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]:
% 12.27/12.53         (~ (v1_xboole_0 @ X1)
% 12.27/12.53          | ~ (zip_tseitin_4 @ X1 @ X0)
% 12.27/12.53          | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ X0) @ X1) @ 
% 12.27/12.53             (u1_pre_topc @ X0)))),
% 12.27/12.53      inference('sup-', [status(thm)], ['75', '76'])).
% 12.27/12.53  thf('78', plain,
% 12.27/12.53      (![X0 : $i]:
% 12.27/12.53         (~ (v1_xboole_0 @ X0)
% 12.27/12.53          | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 12.27/12.53             (u1_pre_topc @ sk_A))
% 12.27/12.53          | ~ (v1_xboole_0 @ X0))),
% 12.27/12.53      inference('sup-', [status(thm)], ['74', '77'])).
% 12.27/12.53  thf('79', plain,
% 12.27/12.53      (![X0 : $i]:
% 12.27/12.53         ((r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 12.27/12.53           (u1_pre_topc @ sk_A))
% 12.27/12.53          | ~ (v1_xboole_0 @ X0))),
% 12.27/12.53      inference('simplify', [status(thm)], ['78'])).
% 12.27/12.53  thf('80', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]:
% 12.27/12.53         ((r2_hidden @ X0 @ (u1_pre_topc @ sk_A))
% 12.27/12.53          | ~ (v1_xboole_0 @ X1)
% 12.27/12.53          | ~ (v1_xboole_0 @ X0)
% 12.27/12.53          | ~ (v1_xboole_0 @ X1))),
% 12.27/12.53      inference('sup+', [status(thm)], ['65', '79'])).
% 12.27/12.53  thf('81', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]:
% 12.27/12.53         (~ (v1_xboole_0 @ X0)
% 12.27/12.53          | ~ (v1_xboole_0 @ X1)
% 12.27/12.53          | (r2_hidden @ X0 @ (u1_pre_topc @ sk_A)))),
% 12.27/12.53      inference('simplify', [status(thm)], ['80'])).
% 12.27/12.53  thf('82', plain,
% 12.27/12.53      (![X0 : $i]:
% 12.27/12.53         ((r2_hidden @ X0 @ (u1_pre_topc @ sk_A)) | ~ (v1_xboole_0 @ X0))),
% 12.27/12.53      inference('condensation', [status(thm)], ['81'])).
% 12.27/12.53  thf('83', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]:
% 12.27/12.53         (~ (l1_pre_topc @ X0)
% 12.27/12.53          | (r2_hidden @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 12.27/12.53          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0)))),
% 12.27/12.53      inference('sup-', [status(thm)], ['12', '13'])).
% 12.27/12.53  thf('84', plain,
% 12.27/12.53      (![X0 : $i]:
% 12.27/12.53         (~ (v1_xboole_0 @ X0)
% 12.27/12.53          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 12.27/12.53          | ~ (l1_pre_topc @ sk_A))),
% 12.27/12.53      inference('sup-', [status(thm)], ['82', '83'])).
% 12.27/12.53  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 12.27/12.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.27/12.53  thf('86', plain,
% 12.27/12.53      (![X0 : $i]:
% 12.27/12.53         (~ (v1_xboole_0 @ X0)
% 12.27/12.53          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 12.27/12.53      inference('demod', [status(thm)], ['84', '85'])).
% 12.27/12.53  thf('87', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 12.27/12.53      inference('sup-', [status(thm)], ['46', '47'])).
% 12.27/12.53  thf('88', plain,
% 12.27/12.53      (![X0 : $i]:
% 12.27/12.53         (~ (v1_xboole_0 @ X0)
% 12.27/12.53          | ~ (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 12.27/12.53      inference('sup-', [status(thm)], ['86', '87'])).
% 12.27/12.53  thf('89', plain, (~ (v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.27/12.53      inference('condensation', [status(thm)], ['88'])).
% 12.27/12.53  thf('90', plain,
% 12.27/12.53      ((m1_subset_1 @ (k3_tarski @ (u1_pre_topc @ sk_A)) @ 
% 12.27/12.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 12.27/12.53      inference('clc', [status(thm)], ['42', '89'])).
% 12.27/12.53  thf('91', plain,
% 12.27/12.53      (![X20 : $i, X21 : $i]:
% 12.27/12.53         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 12.27/12.53      inference('cnf', [status(esa)], [t3_subset])).
% 12.27/12.53  thf('92', plain,
% 12.27/12.53      ((r1_tarski @ (k3_tarski @ (u1_pre_topc @ sk_A)) @ (u1_struct_0 @ sk_A))),
% 12.27/12.53      inference('sup-', [status(thm)], ['90', '91'])).
% 12.27/12.53  thf('93', plain,
% 12.27/12.53      (![X4 : $i, X6 : $i]:
% 12.27/12.53         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 12.27/12.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 12.27/12.53  thf('94', plain,
% 12.27/12.53      ((~ (r1_tarski @ (u1_struct_0 @ sk_A) @ 
% 12.27/12.53           (k3_tarski @ (u1_pre_topc @ sk_A)))
% 12.27/12.53        | ((u1_struct_0 @ sk_A) = (k3_tarski @ (u1_pre_topc @ sk_A))))),
% 12.27/12.53      inference('sup-', [status(thm)], ['92', '93'])).
% 12.27/12.53  thf('95', plain,
% 12.27/12.53      (![X0 : $i]:
% 12.27/12.53         (~ (l1_pre_topc @ X0)
% 12.27/12.53          | ((k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 12.27/12.53              = (k3_tarski @ (u1_pre_topc @ X0))))),
% 12.27/12.53      inference('sup-', [status(thm)], ['0', '1'])).
% 12.27/12.53  thf('96', plain,
% 12.27/12.53      (![X48 : $i, X50 : $i]:
% 12.27/12.53         (~ (v2_pre_topc @ X48)
% 12.27/12.53          | (zip_tseitin_5 @ X50 @ X48)
% 12.27/12.53          | ~ (l1_pre_topc @ X48))),
% 12.27/12.53      inference('cnf', [status(esa)], [zf_stmt_13])).
% 12.27/12.53  thf('97', plain,
% 12.27/12.53      (![X51 : $i]:
% 12.27/12.53         ((m1_subset_1 @ (u1_pre_topc @ X51) @ 
% 12.27/12.53           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51))))
% 12.27/12.53          | ~ (l1_pre_topc @ X51))),
% 12.27/12.53      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 12.27/12.53  thf('98', plain,
% 12.27/12.53      (![X45 : $i, X46 : $i]:
% 12.27/12.53         (~ (m1_subset_1 @ X45 @ 
% 12.27/12.53             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46))))
% 12.27/12.53          | (zip_tseitin_4 @ X45 @ X46)
% 12.27/12.53          | ~ (zip_tseitin_5 @ X45 @ X46))),
% 12.27/12.53      inference('cnf', [status(esa)], [zf_stmt_2])).
% 12.27/12.53  thf('99', plain,
% 12.27/12.53      (![X0 : $i]:
% 12.27/12.53         (~ (l1_pre_topc @ X0)
% 12.27/12.53          | ~ (zip_tseitin_5 @ (u1_pre_topc @ X0) @ X0)
% 12.27/12.53          | (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0))),
% 12.27/12.53      inference('sup-', [status(thm)], ['97', '98'])).
% 12.27/12.53  thf('100', plain,
% 12.27/12.53      (![X0 : $i]:
% 12.27/12.53         (~ (l1_pre_topc @ X0)
% 12.27/12.53          | ~ (v2_pre_topc @ X0)
% 12.27/12.53          | (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0)
% 12.27/12.53          | ~ (l1_pre_topc @ X0))),
% 12.27/12.53      inference('sup-', [status(thm)], ['96', '99'])).
% 12.27/12.53  thf('101', plain,
% 12.27/12.53      (![X0 : $i]:
% 12.27/12.53         ((zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0)
% 12.27/12.53          | ~ (v2_pre_topc @ X0)
% 12.27/12.53          | ~ (l1_pre_topc @ X0))),
% 12.27/12.53      inference('simplify', [status(thm)], ['100'])).
% 12.27/12.53  thf('102', plain,
% 12.27/12.53      (![X0 : $i]:
% 12.27/12.53         (~ (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0)
% 12.27/12.53          | (r2_hidden @ 
% 12.27/12.53             (k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 12.27/12.53             (u1_pre_topc @ X0)))),
% 12.27/12.53      inference('sup-', [status(thm)], ['30', '31'])).
% 12.27/12.53  thf('103', plain,
% 12.27/12.53      (![X0 : $i]:
% 12.27/12.53         (~ (l1_pre_topc @ X0)
% 12.27/12.53          | ~ (v2_pre_topc @ X0)
% 12.27/12.53          | (r2_hidden @ 
% 12.27/12.53             (k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 12.27/12.53             (u1_pre_topc @ X0)))),
% 12.27/12.53      inference('sup-', [status(thm)], ['101', '102'])).
% 12.27/12.53  thf('104', plain,
% 12.27/12.53      (![X0 : $i]:
% 12.27/12.53         ((r2_hidden @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_pre_topc @ X0))
% 12.27/12.53          | ~ (l1_pre_topc @ X0)
% 12.27/12.53          | ~ (v2_pre_topc @ X0)
% 12.27/12.53          | ~ (l1_pre_topc @ X0))),
% 12.27/12.53      inference('sup+', [status(thm)], ['95', '103'])).
% 12.27/12.53  thf('105', plain,
% 12.27/12.53      (![X0 : $i]:
% 12.27/12.53         (~ (v2_pre_topc @ X0)
% 12.27/12.53          | ~ (l1_pre_topc @ X0)
% 12.27/12.53          | (r2_hidden @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_pre_topc @ X0)))),
% 12.27/12.53      inference('simplify', [status(thm)], ['104'])).
% 12.27/12.53  thf(t14_yellow_1, axiom,
% 12.27/12.53    (![A:$i]:
% 12.27/12.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 12.27/12.53       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 12.27/12.53         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 12.27/12.53  thf('106', plain,
% 12.27/12.53      (![X52 : $i]:
% 12.27/12.53         (~ (r2_hidden @ (k3_tarski @ X52) @ X52)
% 12.27/12.53          | ((k4_yellow_0 @ (k2_yellow_1 @ X52)) = (k3_tarski @ X52))
% 12.27/12.53          | (v1_xboole_0 @ X52))),
% 12.27/12.53      inference('cnf', [status(esa)], [t14_yellow_1])).
% 12.27/12.53  thf('107', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 12.27/12.53      inference('sup-', [status(thm)], ['46', '47'])).
% 12.27/12.53  thf('108', plain,
% 12.27/12.53      (![X52 : $i]:
% 12.27/12.53         (((k4_yellow_0 @ (k2_yellow_1 @ X52)) = (k3_tarski @ X52))
% 12.27/12.53          | ~ (r2_hidden @ (k3_tarski @ X52) @ X52))),
% 12.27/12.53      inference('clc', [status(thm)], ['106', '107'])).
% 12.27/12.53  thf('109', plain,
% 12.27/12.53      (![X0 : $i]:
% 12.27/12.53         (~ (l1_pre_topc @ X0)
% 12.27/12.53          | ~ (v2_pre_topc @ X0)
% 12.27/12.53          | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 12.27/12.53              = (k3_tarski @ (u1_pre_topc @ X0))))),
% 12.27/12.53      inference('sup-', [status(thm)], ['105', '108'])).
% 12.27/12.53  thf('110', plain,
% 12.27/12.53      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 12.27/12.53         != (u1_struct_0 @ sk_A))),
% 12.27/12.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.27/12.53  thf('111', plain,
% 12.27/12.53      ((((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))
% 12.27/12.53        | ~ (v2_pre_topc @ sk_A)
% 12.27/12.53        | ~ (l1_pre_topc @ sk_A))),
% 12.27/12.53      inference('sup-', [status(thm)], ['109', '110'])).
% 12.27/12.53  thf('112', plain, ((v2_pre_topc @ sk_A)),
% 12.27/12.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.27/12.53  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 12.27/12.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.27/12.53  thf('114', plain,
% 12.27/12.53      (((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))),
% 12.27/12.53      inference('demod', [status(thm)], ['111', '112', '113'])).
% 12.27/12.53  thf('115', plain,
% 12.27/12.53      (~ (r1_tarski @ (u1_struct_0 @ sk_A) @ (k3_tarski @ (u1_pre_topc @ sk_A)))),
% 12.27/12.53      inference('simplify_reflect-', [status(thm)], ['94', '114'])).
% 12.27/12.53  thf('116', plain,
% 12.27/12.53      ((r2_hidden @ (k3_tarski @ (u1_pre_topc @ sk_A)) @ (u1_pre_topc @ sk_A))),
% 12.27/12.53      inference('demod', [status(thm)], ['34', '35'])).
% 12.27/12.53  thf('117', plain,
% 12.27/12.53      (![X48 : $i]:
% 12.27/12.53         (~ (v2_pre_topc @ X48)
% 12.27/12.53          | (r2_hidden @ (u1_struct_0 @ X48) @ (u1_pre_topc @ X48))
% 12.27/12.53          | ~ (l1_pre_topc @ X48))),
% 12.27/12.53      inference('cnf', [status(esa)], [zf_stmt_13])).
% 12.27/12.53  thf('118', plain,
% 12.27/12.53      (![X26 : $i, X28 : $i, X29 : $i]:
% 12.27/12.53         ((zip_tseitin_0 @ X28 @ X26 @ X29)
% 12.27/12.53          | ~ (r2_hidden @ X28 @ (u1_pre_topc @ X29))
% 12.27/12.53          | ~ (r2_hidden @ X26 @ (u1_pre_topc @ X29)))),
% 12.27/12.53      inference('cnf', [status(esa)], [zf_stmt_12])).
% 12.27/12.53  thf('119', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i]:
% 12.27/12.53         (~ (l1_pre_topc @ X0)
% 12.27/12.53          | ~ (v2_pre_topc @ X0)
% 12.27/12.53          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0))
% 12.27/12.53          | (zip_tseitin_0 @ (u1_struct_0 @ X0) @ X1 @ X0))),
% 12.27/12.53      inference('sup-', [status(thm)], ['117', '118'])).
% 12.27/12.53  thf('120', plain,
% 12.27/12.53      (((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 12.27/12.53         (k3_tarski @ (u1_pre_topc @ sk_A)) @ sk_A)
% 12.27/12.53        | ~ (v2_pre_topc @ sk_A)
% 12.27/12.53        | ~ (l1_pre_topc @ sk_A))),
% 12.27/12.53      inference('sup-', [status(thm)], ['116', '119'])).
% 12.27/12.53  thf('121', plain, ((v2_pre_topc @ sk_A)),
% 12.27/12.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.27/12.53  thf('122', plain, ((l1_pre_topc @ sk_A)),
% 12.27/12.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.27/12.53  thf('123', plain,
% 12.27/12.53      ((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 12.27/12.53        (k3_tarski @ (u1_pre_topc @ sk_A)) @ sk_A)),
% 12.27/12.53      inference('demod', [status(thm)], ['120', '121', '122'])).
% 12.27/12.53  thf('124', plain,
% 12.27/12.53      (![X26 : $i, X27 : $i, X28 : $i]:
% 12.27/12.53         ((r2_hidden @ X28 @ (u1_pre_topc @ X27))
% 12.27/12.53          | ~ (zip_tseitin_0 @ X28 @ X26 @ X27))),
% 12.27/12.53      inference('cnf', [status(esa)], [zf_stmt_12])).
% 12.27/12.53  thf('125', plain,
% 12.27/12.53      ((r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))),
% 12.27/12.53      inference('sup-', [status(thm)], ['123', '124'])).
% 12.27/12.53  thf('126', plain,
% 12.27/12.53      (![X1 : $i, X3 : $i]:
% 12.27/12.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 12.27/12.53      inference('cnf', [status(esa)], [d3_tarski])).
% 12.27/12.53  thf('127', plain,
% 12.27/12.53      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 12.27/12.53         (~ (r2_hidden @ X7 @ X8)
% 12.27/12.53          | ~ (r2_hidden @ X9 @ X7)
% 12.27/12.53          | (r2_hidden @ X9 @ X10)
% 12.27/12.53          | ((X10) != (k3_tarski @ X8)))),
% 12.27/12.53      inference('cnf', [status(esa)], [d4_tarski])).
% 12.27/12.53  thf('128', plain,
% 12.27/12.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 12.27/12.53         ((r2_hidden @ X9 @ (k3_tarski @ X8))
% 12.27/12.53          | ~ (r2_hidden @ X9 @ X7)
% 12.27/12.53          | ~ (r2_hidden @ X7 @ X8))),
% 12.27/12.53      inference('simplify', [status(thm)], ['127'])).
% 12.27/12.53  thf('129', plain,
% 12.27/12.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.27/12.53         ((r1_tarski @ X0 @ X1)
% 12.27/12.53          | ~ (r2_hidden @ X0 @ X2)
% 12.27/12.53          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_tarski @ X2)))),
% 12.27/12.53      inference('sup-', [status(thm)], ['126', '128'])).
% 12.27/12.53  thf('130', plain,
% 12.27/12.53      (![X0 : $i]:
% 12.27/12.53         ((r2_hidden @ (sk_C @ X0 @ (u1_struct_0 @ sk_A)) @ 
% 12.27/12.53           (k3_tarski @ (u1_pre_topc @ sk_A)))
% 12.27/12.53          | (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 12.27/12.53      inference('sup-', [status(thm)], ['125', '129'])).
% 12.27/12.53  thf('131', plain,
% 12.27/12.53      (![X1 : $i, X3 : $i]:
% 12.27/12.53         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 12.27/12.53      inference('cnf', [status(esa)], [d3_tarski])).
% 12.27/12.53  thf('132', plain,
% 12.27/12.53      (((r1_tarski @ (u1_struct_0 @ sk_A) @ (k3_tarski @ (u1_pre_topc @ sk_A)))
% 12.27/12.53        | (r1_tarski @ (u1_struct_0 @ sk_A) @ 
% 12.27/12.53           (k3_tarski @ (u1_pre_topc @ sk_A))))),
% 12.27/12.53      inference('sup-', [status(thm)], ['130', '131'])).
% 12.27/12.53  thf('133', plain,
% 12.27/12.53      ((r1_tarski @ (u1_struct_0 @ sk_A) @ (k3_tarski @ (u1_pre_topc @ sk_A)))),
% 12.27/12.53      inference('simplify', [status(thm)], ['132'])).
% 12.27/12.53  thf('134', plain, ($false), inference('demod', [status(thm)], ['115', '133'])).
% 12.27/12.53  
% 12.27/12.53  % SZS output end Refutation
% 12.27/12.53  
% 12.37/12.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
