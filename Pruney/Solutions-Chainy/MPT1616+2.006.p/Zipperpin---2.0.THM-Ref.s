%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OPonqhWIUV

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:20 EST 2020

% Result     : Theorem 4.00s
% Output     : Refutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 232 expanded)
%              Number of leaves         :   47 (  92 expanded)
%              Depth                    :   23
%              Number of atoms          :  993 (1977 expanded)
%              Number of equality atoms :   19 (  51 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X50: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X50 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) ) )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(redefinition_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k5_setfam_1 @ A @ B )
        = ( k3_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k5_setfam_1 @ X18 @ X17 )
        = ( k3_tarski @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
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
    ! [X47: $i,X49: $i] :
      ( ~ ( v2_pre_topc @ X47 )
      | ( zip_tseitin_5 @ X49 @ X47 )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X41: $i,X43: $i] :
      ( ( zip_tseitin_4 @ X41 @ X43 )
      | ( r1_tarski @ X41 @ ( u1_pre_topc @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
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
    ! [X50: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X50 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) ) )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
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
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
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
    ! [X19: $i,X21: $i] :
      ( ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( zip_tseitin_4 @ X1 @ X0 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) ) )
      | ( zip_tseitin_4 @ X44 @ X45 )
      | ~ ( zip_tseitin_5 @ X44 @ X45 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( r1_tarski @ X41 @ ( u1_pre_topc @ X42 ) )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X42 ) @ X41 ) @ ( u1_pre_topc @ X42 ) )
      | ~ ( zip_tseitin_4 @ X41 @ X42 ) ) ),
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
    ! [X50: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X50 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) ) )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('38',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( m1_subset_1 @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( m1_subset_1 @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('44',plain,(
    r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('48',plain,(
    ! [X47: $i,X49: $i] :
      ( ~ ( v2_pre_topc @ X47 )
      | ( zip_tseitin_5 @ X49 @ X47 )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('49',plain,(
    ! [X50: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X50 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) ) )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('50',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) ) )
      | ( zip_tseitin_4 @ X44 @ X45 )
      | ~ ( zip_tseitin_5 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( zip_tseitin_5 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','55'])).

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
    ! [X51: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X51 ) @ X51 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X51 ) )
        = ( k3_tarski @ X51 ) )
      | ( v1_xboole_0 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('60',plain,(
    ! [X51: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ X51 ) )
        = ( k3_tarski @ X51 ) )
      | ~ ( r2_hidden @ ( k3_tarski @ X51 ) @ X51 ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = ( k3_tarski @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['46','66'])).

thf('68',plain,(
    r2_hidden @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('69',plain,(
    ! [X47: $i] :
      ( ~ ( v2_pre_topc @ X47 )
      | ( r2_hidden @ ( u1_struct_0 @ X47 ) @ ( u1_pre_topc @ X47 ) )
      | ~ ( l1_pre_topc @ X47 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('70',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X25 @ X28 )
      | ~ ( r2_hidden @ X27 @ ( u1_pre_topc @ X28 ) )
      | ~ ( r2_hidden @ X25 @ ( u1_pre_topc @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ X0 ) @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ X27 @ ( u1_pre_topc @ X26 ) )
      | ~ ( zip_tseitin_0 @ X27 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('77',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
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

thf('79',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( r2_hidden @ X12 @ X13 )
      | ( X13
       != ( k3_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('80',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X12 @ ( k3_tarski @ X11 ) )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['78','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) )
      | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','81'])).

thf('83',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('84',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) )
    | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['67','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OPonqhWIUV
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:35:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.21/0.36  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 4.00/4.18  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.00/4.18  % Solved by: fo/fo7.sh
% 4.00/4.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.00/4.18  % done 4551 iterations in 3.733s
% 4.00/4.18  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.00/4.18  % SZS output start Refutation
% 4.00/4.18  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 4.00/4.18  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 4.00/4.18  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 4.00/4.18  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 4.00/4.18  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.00/4.18  thf(sk_A_type, type, sk_A: $i).
% 4.00/4.18  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.00/4.18  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.00/4.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.00/4.18  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 4.00/4.18  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 4.00/4.18  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 4.00/4.18  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.00/4.18  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.00/4.18  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 4.00/4.18  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 4.00/4.18  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 4.00/4.18  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 4.00/4.18  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.00/4.18  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 4.00/4.18  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 4.00/4.18  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.00/4.18  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 4.00/4.18  thf(dt_u1_pre_topc, axiom,
% 4.00/4.18    (![A:$i]:
% 4.00/4.18     ( ( l1_pre_topc @ A ) =>
% 4.00/4.18       ( m1_subset_1 @
% 4.00/4.18         ( u1_pre_topc @ A ) @ 
% 4.00/4.18         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 4.00/4.18  thf('0', plain,
% 4.00/4.18      (![X50 : $i]:
% 4.00/4.18         ((m1_subset_1 @ (u1_pre_topc @ X50) @ 
% 4.00/4.18           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50))))
% 4.00/4.18          | ~ (l1_pre_topc @ X50))),
% 4.00/4.18      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 4.00/4.18  thf(redefinition_k5_setfam_1, axiom,
% 4.00/4.18    (![A:$i,B:$i]:
% 4.00/4.18     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 4.00/4.18       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 4.00/4.18  thf('1', plain,
% 4.00/4.18      (![X17 : $i, X18 : $i]:
% 4.00/4.18         (((k5_setfam_1 @ X18 @ X17) = (k3_tarski @ X17))
% 4.00/4.18          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 4.00/4.18      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 4.00/4.18  thf('2', plain,
% 4.00/4.18      (![X0 : $i]:
% 4.00/4.18         (~ (l1_pre_topc @ X0)
% 4.00/4.18          | ((k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 4.00/4.18              = (k3_tarski @ (u1_pre_topc @ X0))))),
% 4.00/4.18      inference('sup-', [status(thm)], ['0', '1'])).
% 4.00/4.18  thf(t24_yellow_1, conjecture,
% 4.00/4.18    (![A:$i]:
% 4.00/4.18     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.00/4.18       ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 4.00/4.18         ( u1_struct_0 @ A ) ) ))).
% 4.00/4.18  thf(zf_stmt_0, negated_conjecture,
% 4.00/4.18    (~( ![A:$i]:
% 4.00/4.18        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 4.00/4.18            ( l1_pre_topc @ A ) ) =>
% 4.00/4.18          ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 4.00/4.18            ( u1_struct_0 @ A ) ) ) )),
% 4.00/4.18    inference('cnf.neg', [status(esa)], [t24_yellow_1])).
% 4.00/4.18  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf(d1_pre_topc, axiom,
% 4.00/4.18    (![A:$i]:
% 4.00/4.18     ( ( l1_pre_topc @ A ) =>
% 4.00/4.18       ( ( v2_pre_topc @ A ) <=>
% 4.00/4.18         ( ( ![B:$i]:
% 4.00/4.18             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.00/4.18               ( ![C:$i]:
% 4.00/4.18                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.00/4.18                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 4.00/4.18                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 4.00/4.18                     ( r2_hidden @
% 4.00/4.18                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 4.00/4.18                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 4.00/4.18           ( ![B:$i]:
% 4.00/4.18             ( ( m1_subset_1 @
% 4.00/4.18                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.00/4.18               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 4.00/4.18                 ( r2_hidden @
% 4.00/4.18                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 4.00/4.18                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 4.00/4.18           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 4.00/4.18  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $o).
% 4.00/4.18  thf(zf_stmt_2, axiom,
% 4.00/4.18    (![B:$i,A:$i]:
% 4.00/4.18     ( ( zip_tseitin_5 @ B @ A ) <=>
% 4.00/4.18       ( ( m1_subset_1 @
% 4.00/4.18           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.00/4.18         ( zip_tseitin_4 @ B @ A ) ) ))).
% 4.00/4.18  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 4.00/4.18  thf(zf_stmt_4, axiom,
% 4.00/4.18    (![B:$i,A:$i]:
% 4.00/4.18     ( ( zip_tseitin_4 @ B @ A ) <=>
% 4.00/4.18       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 4.00/4.18         ( r2_hidden @
% 4.00/4.18           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 4.00/4.18  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 4.00/4.18  thf(zf_stmt_6, axiom,
% 4.00/4.18    (![B:$i,A:$i]:
% 4.00/4.18     ( ( zip_tseitin_3 @ B @ A ) <=>
% 4.00/4.18       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.00/4.18         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 4.00/4.18  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 4.00/4.18  thf(zf_stmt_8, axiom,
% 4.00/4.18    (![C:$i,B:$i,A:$i]:
% 4.00/4.18     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 4.00/4.18       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.00/4.18         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 4.00/4.18  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.00/4.18  thf(zf_stmt_10, axiom,
% 4.00/4.18    (![C:$i,B:$i,A:$i]:
% 4.00/4.18     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 4.00/4.18       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 4.00/4.18         ( r2_hidden @
% 4.00/4.18           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 4.00/4.18  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 4.00/4.18  thf(zf_stmt_12, axiom,
% 4.00/4.18    (![C:$i,B:$i,A:$i]:
% 4.00/4.18     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 4.00/4.18       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 4.00/4.18         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 4.00/4.18  thf(zf_stmt_13, axiom,
% 4.00/4.18    (![A:$i]:
% 4.00/4.18     ( ( l1_pre_topc @ A ) =>
% 4.00/4.18       ( ( v2_pre_topc @ A ) <=>
% 4.00/4.18         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 4.00/4.18           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 4.00/4.18           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 4.00/4.18  thf('4', plain,
% 4.00/4.18      (![X47 : $i, X49 : $i]:
% 4.00/4.18         (~ (v2_pre_topc @ X47)
% 4.00/4.18          | (zip_tseitin_5 @ X49 @ X47)
% 4.00/4.18          | ~ (l1_pre_topc @ X47))),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_13])).
% 4.00/4.18  thf(d3_tarski, axiom,
% 4.00/4.18    (![A:$i,B:$i]:
% 4.00/4.18     ( ( r1_tarski @ A @ B ) <=>
% 4.00/4.18       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 4.00/4.18  thf('5', plain,
% 4.00/4.18      (![X4 : $i, X6 : $i]:
% 4.00/4.18         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 4.00/4.18      inference('cnf', [status(esa)], [d3_tarski])).
% 4.00/4.18  thf('6', plain,
% 4.00/4.18      (![X41 : $i, X43 : $i]:
% 4.00/4.18         ((zip_tseitin_4 @ X41 @ X43) | (r1_tarski @ X41 @ (u1_pre_topc @ X43)))),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_4])).
% 4.00/4.18  thf('7', plain,
% 4.00/4.18      (![X3 : $i, X4 : $i, X5 : $i]:
% 4.00/4.18         (~ (r2_hidden @ X3 @ X4)
% 4.00/4.18          | (r2_hidden @ X3 @ X5)
% 4.00/4.18          | ~ (r1_tarski @ X4 @ X5))),
% 4.00/4.18      inference('cnf', [status(esa)], [d3_tarski])).
% 4.00/4.18  thf('8', plain,
% 4.00/4.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.18         ((zip_tseitin_4 @ X1 @ X0)
% 4.00/4.18          | (r2_hidden @ X2 @ (u1_pre_topc @ X0))
% 4.00/4.18          | ~ (r2_hidden @ X2 @ X1))),
% 4.00/4.18      inference('sup-', [status(thm)], ['6', '7'])).
% 4.00/4.18  thf('9', plain,
% 4.00/4.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.18         ((r1_tarski @ X0 @ X1)
% 4.00/4.18          | (r2_hidden @ (sk_C @ X1 @ X0) @ (u1_pre_topc @ X2))
% 4.00/4.18          | (zip_tseitin_4 @ X0 @ X2))),
% 4.00/4.18      inference('sup-', [status(thm)], ['5', '8'])).
% 4.00/4.18  thf('10', plain,
% 4.00/4.18      (![X50 : $i]:
% 4.00/4.18         ((m1_subset_1 @ (u1_pre_topc @ X50) @ 
% 4.00/4.18           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50))))
% 4.00/4.18          | ~ (l1_pre_topc @ X50))),
% 4.00/4.18      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 4.00/4.18  thf(t3_subset, axiom,
% 4.00/4.18    (![A:$i,B:$i]:
% 4.00/4.18     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.00/4.18  thf('11', plain,
% 4.00/4.18      (![X19 : $i, X20 : $i]:
% 4.00/4.18         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 4.00/4.18      inference('cnf', [status(esa)], [t3_subset])).
% 4.00/4.18  thf('12', plain,
% 4.00/4.18      (![X0 : $i]:
% 4.00/4.18         (~ (l1_pre_topc @ X0)
% 4.00/4.18          | (r1_tarski @ (u1_pre_topc @ X0) @ 
% 4.00/4.18             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 4.00/4.18      inference('sup-', [status(thm)], ['10', '11'])).
% 4.00/4.18  thf('13', plain,
% 4.00/4.18      (![X3 : $i, X4 : $i, X5 : $i]:
% 4.00/4.18         (~ (r2_hidden @ X3 @ X4)
% 4.00/4.18          | (r2_hidden @ X3 @ X5)
% 4.00/4.18          | ~ (r1_tarski @ X4 @ X5))),
% 4.00/4.18      inference('cnf', [status(esa)], [d3_tarski])).
% 4.00/4.18  thf('14', plain,
% 4.00/4.18      (![X0 : $i, X1 : $i]:
% 4.00/4.18         (~ (l1_pre_topc @ X0)
% 4.00/4.18          | (r2_hidden @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.00/4.18          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0)))),
% 4.00/4.18      inference('sup-', [status(thm)], ['12', '13'])).
% 4.00/4.18  thf('15', plain,
% 4.00/4.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.18         ((zip_tseitin_4 @ X1 @ X0)
% 4.00/4.18          | (r1_tarski @ X1 @ X2)
% 4.00/4.18          | (r2_hidden @ (sk_C @ X2 @ X1) @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.00/4.18          | ~ (l1_pre_topc @ X0))),
% 4.00/4.18      inference('sup-', [status(thm)], ['9', '14'])).
% 4.00/4.18  thf('16', plain,
% 4.00/4.18      (![X4 : $i, X6 : $i]:
% 4.00/4.18         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 4.00/4.18      inference('cnf', [status(esa)], [d3_tarski])).
% 4.00/4.18  thf('17', plain,
% 4.00/4.18      (![X0 : $i, X1 : $i]:
% 4.00/4.18         (~ (l1_pre_topc @ X0)
% 4.00/4.18          | (r1_tarski @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.00/4.18          | (zip_tseitin_4 @ X1 @ X0)
% 4.00/4.18          | (r1_tarski @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 4.00/4.18      inference('sup-', [status(thm)], ['15', '16'])).
% 4.00/4.18  thf('18', plain,
% 4.00/4.18      (![X0 : $i, X1 : $i]:
% 4.00/4.18         ((zip_tseitin_4 @ X1 @ X0)
% 4.00/4.18          | (r1_tarski @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.00/4.18          | ~ (l1_pre_topc @ X0))),
% 4.00/4.18      inference('simplify', [status(thm)], ['17'])).
% 4.00/4.18  thf('19', plain,
% 4.00/4.18      (![X19 : $i, X21 : $i]:
% 4.00/4.18         ((m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X19 @ X21))),
% 4.00/4.18      inference('cnf', [status(esa)], [t3_subset])).
% 4.00/4.18  thf('20', plain,
% 4.00/4.18      (![X0 : $i, X1 : $i]:
% 4.00/4.18         (~ (l1_pre_topc @ X0)
% 4.00/4.18          | (zip_tseitin_4 @ X1 @ X0)
% 4.00/4.18          | (m1_subset_1 @ X1 @ 
% 4.00/4.18             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))),
% 4.00/4.18      inference('sup-', [status(thm)], ['18', '19'])).
% 4.00/4.18  thf('21', plain,
% 4.00/4.18      (![X44 : $i, X45 : $i]:
% 4.00/4.18         (~ (m1_subset_1 @ X44 @ 
% 4.00/4.18             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45))))
% 4.00/4.18          | (zip_tseitin_4 @ X44 @ X45)
% 4.00/4.18          | ~ (zip_tseitin_5 @ X44 @ X45))),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.00/4.18  thf('22', plain,
% 4.00/4.18      (![X0 : $i, X1 : $i]:
% 4.00/4.18         ((zip_tseitin_4 @ X1 @ X0)
% 4.00/4.18          | ~ (l1_pre_topc @ X0)
% 4.00/4.18          | ~ (zip_tseitin_5 @ X1 @ X0)
% 4.00/4.18          | (zip_tseitin_4 @ X1 @ X0))),
% 4.00/4.18      inference('sup-', [status(thm)], ['20', '21'])).
% 4.00/4.18  thf('23', plain,
% 4.00/4.18      (![X0 : $i, X1 : $i]:
% 4.00/4.18         (~ (zip_tseitin_5 @ X1 @ X0)
% 4.00/4.18          | ~ (l1_pre_topc @ X0)
% 4.00/4.18          | (zip_tseitin_4 @ X1 @ X0))),
% 4.00/4.18      inference('simplify', [status(thm)], ['22'])).
% 4.00/4.18  thf('24', plain,
% 4.00/4.18      (![X0 : $i, X1 : $i]:
% 4.00/4.18         (~ (l1_pre_topc @ X0)
% 4.00/4.18          | ~ (v2_pre_topc @ X0)
% 4.00/4.18          | (zip_tseitin_4 @ X1 @ X0)
% 4.00/4.18          | ~ (l1_pre_topc @ X0))),
% 4.00/4.18      inference('sup-', [status(thm)], ['4', '23'])).
% 4.00/4.18  thf('25', plain,
% 4.00/4.18      (![X0 : $i, X1 : $i]:
% 4.00/4.18         ((zip_tseitin_4 @ X1 @ X0)
% 4.00/4.18          | ~ (v2_pre_topc @ X0)
% 4.00/4.18          | ~ (l1_pre_topc @ X0))),
% 4.00/4.18      inference('simplify', [status(thm)], ['24'])).
% 4.00/4.18  thf('26', plain,
% 4.00/4.18      (![X0 : $i]: (~ (v2_pre_topc @ sk_A) | (zip_tseitin_4 @ X0 @ sk_A))),
% 4.00/4.18      inference('sup-', [status(thm)], ['3', '25'])).
% 4.00/4.18  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf('28', plain, (![X0 : $i]: (zip_tseitin_4 @ X0 @ sk_A)),
% 4.00/4.18      inference('demod', [status(thm)], ['26', '27'])).
% 4.00/4.18  thf(d10_xboole_0, axiom,
% 4.00/4.18    (![A:$i,B:$i]:
% 4.00/4.18     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.00/4.18  thf('29', plain,
% 4.00/4.18      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 4.00/4.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.00/4.18  thf('30', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 4.00/4.18      inference('simplify', [status(thm)], ['29'])).
% 4.00/4.18  thf('31', plain,
% 4.00/4.18      (![X41 : $i, X42 : $i]:
% 4.00/4.18         (~ (r1_tarski @ X41 @ (u1_pre_topc @ X42))
% 4.00/4.18          | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ X42) @ X41) @ 
% 4.00/4.18             (u1_pre_topc @ X42))
% 4.00/4.18          | ~ (zip_tseitin_4 @ X41 @ X42))),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_4])).
% 4.00/4.18  thf('32', plain,
% 4.00/4.18      (![X0 : $i]:
% 4.00/4.18         (~ (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0)
% 4.00/4.18          | (r2_hidden @ 
% 4.00/4.18             (k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 4.00/4.18             (u1_pre_topc @ X0)))),
% 4.00/4.18      inference('sup-', [status(thm)], ['30', '31'])).
% 4.00/4.18  thf('33', plain,
% 4.00/4.18      ((r2_hidden @ 
% 4.00/4.18        (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 4.00/4.18        (u1_pre_topc @ sk_A))),
% 4.00/4.18      inference('sup-', [status(thm)], ['28', '32'])).
% 4.00/4.18  thf('34', plain,
% 4.00/4.18      (((r2_hidden @ (k3_tarski @ (u1_pre_topc @ sk_A)) @ (u1_pre_topc @ sk_A))
% 4.00/4.18        | ~ (l1_pre_topc @ sk_A))),
% 4.00/4.18      inference('sup+', [status(thm)], ['2', '33'])).
% 4.00/4.18  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf('36', plain,
% 4.00/4.18      ((r2_hidden @ (k3_tarski @ (u1_pre_topc @ sk_A)) @ (u1_pre_topc @ sk_A))),
% 4.00/4.18      inference('demod', [status(thm)], ['34', '35'])).
% 4.00/4.18  thf('37', plain,
% 4.00/4.18      (![X50 : $i]:
% 4.00/4.18         ((m1_subset_1 @ (u1_pre_topc @ X50) @ 
% 4.00/4.18           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50))))
% 4.00/4.18          | ~ (l1_pre_topc @ X50))),
% 4.00/4.18      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 4.00/4.18  thf(t4_subset, axiom,
% 4.00/4.18    (![A:$i,B:$i,C:$i]:
% 4.00/4.18     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 4.00/4.18       ( m1_subset_1 @ A @ C ) ))).
% 4.00/4.18  thf('38', plain,
% 4.00/4.18      (![X22 : $i, X23 : $i, X24 : $i]:
% 4.00/4.18         (~ (r2_hidden @ X22 @ X23)
% 4.00/4.18          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 4.00/4.18          | (m1_subset_1 @ X22 @ X24))),
% 4.00/4.18      inference('cnf', [status(esa)], [t4_subset])).
% 4.00/4.18  thf('39', plain,
% 4.00/4.18      (![X0 : $i, X1 : $i]:
% 4.00/4.18         (~ (l1_pre_topc @ X0)
% 4.00/4.18          | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.00/4.18          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0)))),
% 4.00/4.18      inference('sup-', [status(thm)], ['37', '38'])).
% 4.00/4.18  thf('40', plain,
% 4.00/4.18      (((m1_subset_1 @ (k3_tarski @ (u1_pre_topc @ sk_A)) @ 
% 4.00/4.18         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.00/4.18        | ~ (l1_pre_topc @ sk_A))),
% 4.00/4.18      inference('sup-', [status(thm)], ['36', '39'])).
% 4.00/4.18  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf('42', plain,
% 4.00/4.18      ((m1_subset_1 @ (k3_tarski @ (u1_pre_topc @ sk_A)) @ 
% 4.00/4.18        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 4.00/4.18      inference('demod', [status(thm)], ['40', '41'])).
% 4.00/4.18  thf('43', plain,
% 4.00/4.18      (![X19 : $i, X20 : $i]:
% 4.00/4.18         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 4.00/4.18      inference('cnf', [status(esa)], [t3_subset])).
% 4.00/4.18  thf('44', plain,
% 4.00/4.18      ((r1_tarski @ (k3_tarski @ (u1_pre_topc @ sk_A)) @ (u1_struct_0 @ sk_A))),
% 4.00/4.18      inference('sup-', [status(thm)], ['42', '43'])).
% 4.00/4.18  thf('45', plain,
% 4.00/4.18      (![X7 : $i, X9 : $i]:
% 4.00/4.18         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 4.00/4.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.00/4.18  thf('46', plain,
% 4.00/4.18      ((~ (r1_tarski @ (u1_struct_0 @ sk_A) @ 
% 4.00/4.18           (k3_tarski @ (u1_pre_topc @ sk_A)))
% 4.00/4.18        | ((u1_struct_0 @ sk_A) = (k3_tarski @ (u1_pre_topc @ sk_A))))),
% 4.00/4.18      inference('sup-', [status(thm)], ['44', '45'])).
% 4.00/4.18  thf('47', plain,
% 4.00/4.18      (![X0 : $i]:
% 4.00/4.18         (~ (l1_pre_topc @ X0)
% 4.00/4.18          | ((k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 4.00/4.18              = (k3_tarski @ (u1_pre_topc @ X0))))),
% 4.00/4.18      inference('sup-', [status(thm)], ['0', '1'])).
% 4.00/4.18  thf('48', plain,
% 4.00/4.18      (![X47 : $i, X49 : $i]:
% 4.00/4.18         (~ (v2_pre_topc @ X47)
% 4.00/4.18          | (zip_tseitin_5 @ X49 @ X47)
% 4.00/4.18          | ~ (l1_pre_topc @ X47))),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_13])).
% 4.00/4.18  thf('49', plain,
% 4.00/4.18      (![X50 : $i]:
% 4.00/4.18         ((m1_subset_1 @ (u1_pre_topc @ X50) @ 
% 4.00/4.18           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50))))
% 4.00/4.18          | ~ (l1_pre_topc @ X50))),
% 4.00/4.18      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 4.00/4.18  thf('50', plain,
% 4.00/4.18      (![X44 : $i, X45 : $i]:
% 4.00/4.18         (~ (m1_subset_1 @ X44 @ 
% 4.00/4.18             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45))))
% 4.00/4.18          | (zip_tseitin_4 @ X44 @ X45)
% 4.00/4.18          | ~ (zip_tseitin_5 @ X44 @ X45))),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.00/4.18  thf('51', plain,
% 4.00/4.18      (![X0 : $i]:
% 4.00/4.18         (~ (l1_pre_topc @ X0)
% 4.00/4.18          | ~ (zip_tseitin_5 @ (u1_pre_topc @ X0) @ X0)
% 4.00/4.18          | (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0))),
% 4.00/4.18      inference('sup-', [status(thm)], ['49', '50'])).
% 4.00/4.18  thf('52', plain,
% 4.00/4.18      (![X0 : $i]:
% 4.00/4.18         (~ (l1_pre_topc @ X0)
% 4.00/4.18          | ~ (v2_pre_topc @ X0)
% 4.00/4.18          | (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0)
% 4.00/4.18          | ~ (l1_pre_topc @ X0))),
% 4.00/4.18      inference('sup-', [status(thm)], ['48', '51'])).
% 4.00/4.18  thf('53', plain,
% 4.00/4.18      (![X0 : $i]:
% 4.00/4.18         ((zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0)
% 4.00/4.18          | ~ (v2_pre_topc @ X0)
% 4.00/4.18          | ~ (l1_pre_topc @ X0))),
% 4.00/4.18      inference('simplify', [status(thm)], ['52'])).
% 4.00/4.18  thf('54', plain,
% 4.00/4.18      (![X0 : $i]:
% 4.00/4.18         (~ (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0)
% 4.00/4.18          | (r2_hidden @ 
% 4.00/4.18             (k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 4.00/4.18             (u1_pre_topc @ X0)))),
% 4.00/4.18      inference('sup-', [status(thm)], ['30', '31'])).
% 4.00/4.18  thf('55', plain,
% 4.00/4.18      (![X0 : $i]:
% 4.00/4.18         (~ (l1_pre_topc @ X0)
% 4.00/4.18          | ~ (v2_pre_topc @ X0)
% 4.00/4.18          | (r2_hidden @ 
% 4.00/4.18             (k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 4.00/4.18             (u1_pre_topc @ X0)))),
% 4.00/4.18      inference('sup-', [status(thm)], ['53', '54'])).
% 4.00/4.18  thf('56', plain,
% 4.00/4.18      (![X0 : $i]:
% 4.00/4.18         ((r2_hidden @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_pre_topc @ X0))
% 4.00/4.18          | ~ (l1_pre_topc @ X0)
% 4.00/4.18          | ~ (v2_pre_topc @ X0)
% 4.00/4.18          | ~ (l1_pre_topc @ X0))),
% 4.00/4.18      inference('sup+', [status(thm)], ['47', '55'])).
% 4.00/4.18  thf('57', plain,
% 4.00/4.18      (![X0 : $i]:
% 4.00/4.18         (~ (v2_pre_topc @ X0)
% 4.00/4.18          | ~ (l1_pre_topc @ X0)
% 4.00/4.18          | (r2_hidden @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_pre_topc @ X0)))),
% 4.00/4.18      inference('simplify', [status(thm)], ['56'])).
% 4.00/4.18  thf(t14_yellow_1, axiom,
% 4.00/4.18    (![A:$i]:
% 4.00/4.18     ( ( ~( v1_xboole_0 @ A ) ) =>
% 4.00/4.18       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 4.00/4.18         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 4.00/4.18  thf('58', plain,
% 4.00/4.18      (![X51 : $i]:
% 4.00/4.18         (~ (r2_hidden @ (k3_tarski @ X51) @ X51)
% 4.00/4.18          | ((k4_yellow_0 @ (k2_yellow_1 @ X51)) = (k3_tarski @ X51))
% 4.00/4.18          | (v1_xboole_0 @ X51))),
% 4.00/4.18      inference('cnf', [status(esa)], [t14_yellow_1])).
% 4.00/4.18  thf(d1_xboole_0, axiom,
% 4.00/4.18    (![A:$i]:
% 4.00/4.18     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 4.00/4.18  thf('59', plain,
% 4.00/4.18      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 4.00/4.18      inference('cnf', [status(esa)], [d1_xboole_0])).
% 4.00/4.18  thf('60', plain,
% 4.00/4.18      (![X51 : $i]:
% 4.00/4.18         (((k4_yellow_0 @ (k2_yellow_1 @ X51)) = (k3_tarski @ X51))
% 4.00/4.18          | ~ (r2_hidden @ (k3_tarski @ X51) @ X51))),
% 4.00/4.18      inference('clc', [status(thm)], ['58', '59'])).
% 4.00/4.18  thf('61', plain,
% 4.00/4.18      (![X0 : $i]:
% 4.00/4.18         (~ (l1_pre_topc @ X0)
% 4.00/4.18          | ~ (v2_pre_topc @ X0)
% 4.00/4.18          | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ X0)))
% 4.00/4.18              = (k3_tarski @ (u1_pre_topc @ X0))))),
% 4.00/4.18      inference('sup-', [status(thm)], ['57', '60'])).
% 4.00/4.18  thf('62', plain,
% 4.00/4.18      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 4.00/4.18         != (u1_struct_0 @ sk_A))),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf('63', plain,
% 4.00/4.18      ((((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))
% 4.00/4.18        | ~ (v2_pre_topc @ sk_A)
% 4.00/4.18        | ~ (l1_pre_topc @ sk_A))),
% 4.00/4.18      inference('sup-', [status(thm)], ['61', '62'])).
% 4.00/4.18  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf('66', plain,
% 4.00/4.18      (((k3_tarski @ (u1_pre_topc @ sk_A)) != (u1_struct_0 @ sk_A))),
% 4.00/4.18      inference('demod', [status(thm)], ['63', '64', '65'])).
% 4.00/4.18  thf('67', plain,
% 4.00/4.18      (~ (r1_tarski @ (u1_struct_0 @ sk_A) @ (k3_tarski @ (u1_pre_topc @ sk_A)))),
% 4.00/4.18      inference('simplify_reflect-', [status(thm)], ['46', '66'])).
% 4.00/4.18  thf('68', plain,
% 4.00/4.18      ((r2_hidden @ (k3_tarski @ (u1_pre_topc @ sk_A)) @ (u1_pre_topc @ sk_A))),
% 4.00/4.18      inference('demod', [status(thm)], ['34', '35'])).
% 4.00/4.18  thf('69', plain,
% 4.00/4.18      (![X47 : $i]:
% 4.00/4.18         (~ (v2_pre_topc @ X47)
% 4.00/4.18          | (r2_hidden @ (u1_struct_0 @ X47) @ (u1_pre_topc @ X47))
% 4.00/4.18          | ~ (l1_pre_topc @ X47))),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_13])).
% 4.00/4.18  thf('70', plain,
% 4.00/4.18      (![X25 : $i, X27 : $i, X28 : $i]:
% 4.00/4.18         ((zip_tseitin_0 @ X27 @ X25 @ X28)
% 4.00/4.18          | ~ (r2_hidden @ X27 @ (u1_pre_topc @ X28))
% 4.00/4.18          | ~ (r2_hidden @ X25 @ (u1_pre_topc @ X28)))),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_12])).
% 4.00/4.18  thf('71', plain,
% 4.00/4.18      (![X0 : $i, X1 : $i]:
% 4.00/4.18         (~ (l1_pre_topc @ X0)
% 4.00/4.18          | ~ (v2_pre_topc @ X0)
% 4.00/4.18          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0))
% 4.00/4.18          | (zip_tseitin_0 @ (u1_struct_0 @ X0) @ X1 @ X0))),
% 4.00/4.18      inference('sup-', [status(thm)], ['69', '70'])).
% 4.00/4.18  thf('72', plain,
% 4.00/4.18      (((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 4.00/4.18         (k3_tarski @ (u1_pre_topc @ sk_A)) @ sk_A)
% 4.00/4.18        | ~ (v2_pre_topc @ sk_A)
% 4.00/4.18        | ~ (l1_pre_topc @ sk_A))),
% 4.00/4.18      inference('sup-', [status(thm)], ['68', '71'])).
% 4.00/4.18  thf('73', plain, ((v2_pre_topc @ sk_A)),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.00/4.18  thf('75', plain,
% 4.00/4.18      ((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 4.00/4.18        (k3_tarski @ (u1_pre_topc @ sk_A)) @ sk_A)),
% 4.00/4.18      inference('demod', [status(thm)], ['72', '73', '74'])).
% 4.00/4.18  thf('76', plain,
% 4.00/4.18      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.00/4.18         ((r2_hidden @ X27 @ (u1_pre_topc @ X26))
% 4.00/4.18          | ~ (zip_tseitin_0 @ X27 @ X25 @ X26))),
% 4.00/4.18      inference('cnf', [status(esa)], [zf_stmt_12])).
% 4.00/4.18  thf('77', plain, ((r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))),
% 4.00/4.18      inference('sup-', [status(thm)], ['75', '76'])).
% 4.00/4.18  thf('78', plain,
% 4.00/4.18      (![X4 : $i, X6 : $i]:
% 4.00/4.18         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 4.00/4.18      inference('cnf', [status(esa)], [d3_tarski])).
% 4.00/4.18  thf(d4_tarski, axiom,
% 4.00/4.18    (![A:$i,B:$i]:
% 4.00/4.18     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 4.00/4.18       ( ![C:$i]:
% 4.00/4.18         ( ( r2_hidden @ C @ B ) <=>
% 4.00/4.18           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 4.00/4.18  thf('79', plain,
% 4.00/4.18      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 4.00/4.18         (~ (r2_hidden @ X10 @ X11)
% 4.00/4.18          | ~ (r2_hidden @ X12 @ X10)
% 4.00/4.18          | (r2_hidden @ X12 @ X13)
% 4.00/4.18          | ((X13) != (k3_tarski @ X11)))),
% 4.00/4.18      inference('cnf', [status(esa)], [d4_tarski])).
% 4.00/4.18  thf('80', plain,
% 4.00/4.18      (![X10 : $i, X11 : $i, X12 : $i]:
% 4.00/4.18         ((r2_hidden @ X12 @ (k3_tarski @ X11))
% 4.00/4.18          | ~ (r2_hidden @ X12 @ X10)
% 4.00/4.18          | ~ (r2_hidden @ X10 @ X11))),
% 4.00/4.18      inference('simplify', [status(thm)], ['79'])).
% 4.00/4.18  thf('81', plain,
% 4.00/4.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.00/4.18         ((r1_tarski @ X0 @ X1)
% 4.00/4.18          | ~ (r2_hidden @ X0 @ X2)
% 4.00/4.18          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_tarski @ X2)))),
% 4.00/4.18      inference('sup-', [status(thm)], ['78', '80'])).
% 4.00/4.18  thf('82', plain,
% 4.00/4.18      (![X0 : $i]:
% 4.00/4.18         ((r2_hidden @ (sk_C @ X0 @ (u1_struct_0 @ sk_A)) @ 
% 4.00/4.18           (k3_tarski @ (u1_pre_topc @ sk_A)))
% 4.00/4.18          | (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 4.00/4.18      inference('sup-', [status(thm)], ['77', '81'])).
% 4.00/4.18  thf('83', plain,
% 4.00/4.18      (![X4 : $i, X6 : $i]:
% 4.00/4.18         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 4.00/4.18      inference('cnf', [status(esa)], [d3_tarski])).
% 4.00/4.18  thf('84', plain,
% 4.00/4.18      (((r1_tarski @ (u1_struct_0 @ sk_A) @ (k3_tarski @ (u1_pre_topc @ sk_A)))
% 4.00/4.18        | (r1_tarski @ (u1_struct_0 @ sk_A) @ 
% 4.00/4.18           (k3_tarski @ (u1_pre_topc @ sk_A))))),
% 4.00/4.18      inference('sup-', [status(thm)], ['82', '83'])).
% 4.00/4.18  thf('85', plain,
% 4.00/4.18      ((r1_tarski @ (u1_struct_0 @ sk_A) @ (k3_tarski @ (u1_pre_topc @ sk_A)))),
% 4.00/4.18      inference('simplify', [status(thm)], ['84'])).
% 4.00/4.18  thf('86', plain, ($false), inference('demod', [status(thm)], ['67', '85'])).
% 4.00/4.18  
% 4.00/4.18  % SZS output end Refutation
% 4.00/4.18  
% 4.00/4.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
