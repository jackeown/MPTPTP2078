%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YmGFpQlbrG

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:21 EST 2020

% Result     : Theorem 20.71s
% Output     : Refutation 20.71s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 237 expanded)
%              Number of leaves         :   47 (  95 expanded)
%              Depth                    :   17
%              Number of atoms          :  680 (1989 expanded)
%              Number of equality atoms :   17 (  62 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X12 ) @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X13 @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X43: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X43 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( u1_pre_topc @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ ( k3_tarski @ X11 ) )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( sk_C_1 @ X1 @ ( u1_pre_topc @ X0 ) ) @ ( k3_tarski @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('9',plain,(
    ! [X14: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( sk_C_1 @ X1 @ ( u1_pre_topc @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X12 ) @ X13 )
      | ~ ( r1_tarski @ ( sk_C_1 @ X13 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

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

thf('14',plain,(
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

thf('15',plain,(
    ! [X40: $i,X42: $i] :
      ( ~ ( v2_pre_topc @ X40 )
      | ( zip_tseitin_5 @ X42 @ X40 )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_5 @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( zip_tseitin_5 @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X43: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X43 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('20',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) ) )
      | ( zip_tseitin_4 @ X37 @ X38 )
      | ~ ( zip_tseitin_5 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( zip_tseitin_5 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( zip_tseitin_4 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    zip_tseitin_4 @ ( u1_pre_topc @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['22','23'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ X34 @ ( u1_pre_topc @ X35 ) )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X35 ) @ X34 ) @ ( u1_pre_topc @ X35 ) )
      | ~ ( zip_tseitin_4 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_4 @ ( u1_pre_topc @ X0 ) @ X0 )
      | ( r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    ! [X40: $i] :
      ( ~ ( v2_pre_topc @ X40 )
      | ( r2_hidden @ ( u1_struct_0 @ X40 ) @ ( u1_pre_topc @ X40 ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('31',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X18 @ X21 )
      | ~ ( r2_hidden @ X20 @ ( u1_pre_topc @ X21 ) )
      | ~ ( r2_hidden @ X18 @ ( u1_pre_topc @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ X0 ) @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( k5_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X20 @ ( u1_pre_topc @ X19 ) )
      | ~ ( zip_tseitin_0 @ X20 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('38',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ ( k3_tarski @ X11 ) )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('40',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,
    ( ~ ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('46',plain,(
    ! [X44: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X44 ) @ X44 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X44 ) )
        = ( k3_tarski @ X44 ) )
      | ( v1_xboole_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('48',plain,(
    ! [X44: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ X44 ) )
        = ( k3_tarski @ X44 ) )
      | ~ ( r2_hidden @ ( k3_tarski @ X44 ) @ X44 ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
      = ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('51',plain,
    ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('52',plain,
    ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YmGFpQlbrG
% 0.14/0.36  % Computer   : n006.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 10:22:52 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 20.71/20.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 20.71/20.95  % Solved by: fo/fo7.sh
% 20.71/20.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 20.71/20.95  % done 7068 iterations in 20.474s
% 20.71/20.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 20.71/20.95  % SZS output start Refutation
% 20.71/20.95  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 20.71/20.95  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 20.71/20.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 20.71/20.95  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 20.71/20.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 20.71/20.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 20.71/20.95  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 20.71/20.95  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 20.71/20.95  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 20.71/20.95  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 20.71/20.95  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 20.71/20.95  thf(sk_A_type, type, sk_A: $i).
% 20.71/20.95  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 20.71/20.95  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 20.71/20.95  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 20.71/20.95  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 20.71/20.95  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 20.71/20.95  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 20.71/20.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 20.71/20.95  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 20.71/20.95  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 20.71/20.95  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 20.71/20.95  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 20.71/20.95  thf(t94_zfmisc_1, axiom,
% 20.71/20.95    (![A:$i,B:$i]:
% 20.71/20.95     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 20.71/20.95       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 20.71/20.95  thf('0', plain,
% 20.71/20.95      (![X12 : $i, X13 : $i]:
% 20.71/20.95         ((r1_tarski @ (k3_tarski @ X12) @ X13)
% 20.71/20.95          | (r2_hidden @ (sk_C_1 @ X13 @ X12) @ X12))),
% 20.71/20.95      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 20.71/20.95  thf(dt_u1_pre_topc, axiom,
% 20.71/20.95    (![A:$i]:
% 20.71/20.95     ( ( l1_pre_topc @ A ) =>
% 20.71/20.95       ( m1_subset_1 @
% 20.71/20.95         ( u1_pre_topc @ A ) @ 
% 20.71/20.95         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 20.71/20.95  thf('1', plain,
% 20.71/20.95      (![X43 : $i]:
% 20.71/20.95         ((m1_subset_1 @ (u1_pre_topc @ X43) @ 
% 20.71/20.95           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43))))
% 20.71/20.95          | ~ (l1_pre_topc @ X43))),
% 20.71/20.95      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 20.71/20.95  thf(t3_subset, axiom,
% 20.71/20.95    (![A:$i,B:$i]:
% 20.71/20.95     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 20.71/20.95  thf('2', plain,
% 20.71/20.95      (![X15 : $i, X16 : $i]:
% 20.71/20.95         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 20.71/20.95      inference('cnf', [status(esa)], [t3_subset])).
% 20.71/20.95  thf('3', plain,
% 20.71/20.95      (![X0 : $i]:
% 20.71/20.95         (~ (l1_pre_topc @ X0)
% 20.71/20.95          | (r1_tarski @ (u1_pre_topc @ X0) @ 
% 20.71/20.95             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 20.71/20.95      inference('sup-', [status(thm)], ['1', '2'])).
% 20.71/20.95  thf(d3_tarski, axiom,
% 20.71/20.95    (![A:$i,B:$i]:
% 20.71/20.95     ( ( r1_tarski @ A @ B ) <=>
% 20.71/20.95       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 20.71/20.95  thf('4', plain,
% 20.71/20.95      (![X3 : $i, X4 : $i, X5 : $i]:
% 20.71/20.95         (~ (r2_hidden @ X3 @ X4)
% 20.71/20.95          | (r2_hidden @ X3 @ X5)
% 20.71/20.95          | ~ (r1_tarski @ X4 @ X5))),
% 20.71/20.95      inference('cnf', [status(esa)], [d3_tarski])).
% 20.71/20.95  thf('5', plain,
% 20.71/20.95      (![X0 : $i, X1 : $i]:
% 20.71/20.95         (~ (l1_pre_topc @ X0)
% 20.71/20.95          | (r2_hidden @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 20.71/20.95          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0)))),
% 20.71/20.95      inference('sup-', [status(thm)], ['3', '4'])).
% 20.71/20.95  thf('6', plain,
% 20.71/20.95      (![X0 : $i, X1 : $i]:
% 20.71/20.95         ((r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ X1)
% 20.71/20.95          | (r2_hidden @ (sk_C_1 @ X1 @ (u1_pre_topc @ X0)) @ 
% 20.71/20.95             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 20.71/20.95          | ~ (l1_pre_topc @ X0))),
% 20.71/20.95      inference('sup-', [status(thm)], ['0', '5'])).
% 20.71/20.95  thf(l49_zfmisc_1, axiom,
% 20.71/20.95    (![A:$i,B:$i]:
% 20.71/20.95     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 20.71/20.95  thf('7', plain,
% 20.71/20.95      (![X10 : $i, X11 : $i]:
% 20.71/20.95         ((r1_tarski @ X10 @ (k3_tarski @ X11)) | ~ (r2_hidden @ X10 @ X11))),
% 20.71/20.95      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 20.71/20.95  thf('8', plain,
% 20.71/20.95      (![X0 : $i, X1 : $i]:
% 20.71/20.95         (~ (l1_pre_topc @ X0)
% 20.71/20.95          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ X1)
% 20.71/20.95          | (r1_tarski @ (sk_C_1 @ X1 @ (u1_pre_topc @ X0)) @ 
% 20.71/20.95             (k3_tarski @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))),
% 20.71/20.95      inference('sup-', [status(thm)], ['6', '7'])).
% 20.71/20.95  thf(t99_zfmisc_1, axiom,
% 20.71/20.95    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 20.71/20.95  thf('9', plain, (![X14 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X14)) = (X14))),
% 20.71/20.95      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 20.71/20.95  thf('10', plain,
% 20.71/20.95      (![X0 : $i, X1 : $i]:
% 20.71/20.95         (~ (l1_pre_topc @ X0)
% 20.71/20.95          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ X1)
% 20.71/20.95          | (r1_tarski @ (sk_C_1 @ X1 @ (u1_pre_topc @ X0)) @ 
% 20.71/20.95             (u1_struct_0 @ X0)))),
% 20.71/20.95      inference('demod', [status(thm)], ['8', '9'])).
% 20.71/20.95  thf('11', plain,
% 20.71/20.95      (![X12 : $i, X13 : $i]:
% 20.71/20.95         ((r1_tarski @ (k3_tarski @ X12) @ X13)
% 20.71/20.95          | ~ (r1_tarski @ (sk_C_1 @ X13 @ X12) @ X13))),
% 20.71/20.95      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 20.71/20.95  thf('12', plain,
% 20.71/20.95      (![X0 : $i]:
% 20.71/20.95         ((r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_struct_0 @ X0))
% 20.71/20.95          | ~ (l1_pre_topc @ X0)
% 20.71/20.95          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_struct_0 @ X0)))),
% 20.71/20.95      inference('sup-', [status(thm)], ['10', '11'])).
% 20.71/20.95  thf('13', plain,
% 20.71/20.95      (![X0 : $i]:
% 20.71/20.95         (~ (l1_pre_topc @ X0)
% 20.71/20.95          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_struct_0 @ X0)))),
% 20.71/20.95      inference('simplify', [status(thm)], ['12'])).
% 20.71/20.95  thf(t24_yellow_1, conjecture,
% 20.71/20.95    (![A:$i]:
% 20.71/20.95     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 20.71/20.95       ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 20.71/20.95         ( u1_struct_0 @ A ) ) ))).
% 20.71/20.95  thf(zf_stmt_0, negated_conjecture,
% 20.71/20.95    (~( ![A:$i]:
% 20.71/20.95        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 20.71/20.95            ( l1_pre_topc @ A ) ) =>
% 20.71/20.95          ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 20.71/20.95            ( u1_struct_0 @ A ) ) ) )),
% 20.71/20.95    inference('cnf.neg', [status(esa)], [t24_yellow_1])).
% 20.71/20.95  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 20.71/20.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.71/20.95  thf(d1_pre_topc, axiom,
% 20.71/20.95    (![A:$i]:
% 20.71/20.95     ( ( l1_pre_topc @ A ) =>
% 20.71/20.95       ( ( v2_pre_topc @ A ) <=>
% 20.71/20.95         ( ( ![B:$i]:
% 20.71/20.95             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 20.71/20.95               ( ![C:$i]:
% 20.71/20.95                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 20.71/20.95                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 20.71/20.95                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 20.71/20.95                     ( r2_hidden @
% 20.71/20.95                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 20.71/20.95                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 20.71/20.95           ( ![B:$i]:
% 20.71/20.95             ( ( m1_subset_1 @
% 20.71/20.95                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 20.71/20.95               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 20.71/20.95                 ( r2_hidden @
% 20.71/20.95                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 20.71/20.95                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 20.71/20.95           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 20.71/20.95  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $o).
% 20.71/20.95  thf(zf_stmt_2, axiom,
% 20.71/20.95    (![B:$i,A:$i]:
% 20.71/20.95     ( ( zip_tseitin_5 @ B @ A ) <=>
% 20.71/20.95       ( ( m1_subset_1 @
% 20.71/20.95           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 20.71/20.95         ( zip_tseitin_4 @ B @ A ) ) ))).
% 20.71/20.95  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 20.71/20.95  thf(zf_stmt_4, axiom,
% 20.71/20.95    (![B:$i,A:$i]:
% 20.71/20.95     ( ( zip_tseitin_4 @ B @ A ) <=>
% 20.71/20.95       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 20.71/20.95         ( r2_hidden @
% 20.71/20.95           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 20.71/20.95  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 20.71/20.95  thf(zf_stmt_6, axiom,
% 20.71/20.95    (![B:$i,A:$i]:
% 20.71/20.95     ( ( zip_tseitin_3 @ B @ A ) <=>
% 20.71/20.95       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 20.71/20.95         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 20.71/20.95  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 20.71/20.95  thf(zf_stmt_8, axiom,
% 20.71/20.95    (![C:$i,B:$i,A:$i]:
% 20.71/20.95     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 20.71/20.95       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 20.71/20.95         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 20.71/20.95  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 20.71/20.95  thf(zf_stmt_10, axiom,
% 20.71/20.95    (![C:$i,B:$i,A:$i]:
% 20.71/20.95     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 20.71/20.95       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 20.71/20.95         ( r2_hidden @
% 20.71/20.95           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 20.71/20.95  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 20.71/20.95  thf(zf_stmt_12, axiom,
% 20.71/20.95    (![C:$i,B:$i,A:$i]:
% 20.71/20.95     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 20.71/20.95       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 20.71/20.95         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 20.71/20.95  thf(zf_stmt_13, axiom,
% 20.71/20.95    (![A:$i]:
% 20.71/20.95     ( ( l1_pre_topc @ A ) =>
% 20.71/20.95       ( ( v2_pre_topc @ A ) <=>
% 20.71/20.95         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 20.71/20.95           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 20.71/20.95           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 20.71/20.95  thf('15', plain,
% 20.71/20.95      (![X40 : $i, X42 : $i]:
% 20.71/20.95         (~ (v2_pre_topc @ X40)
% 20.71/20.95          | (zip_tseitin_5 @ X42 @ X40)
% 20.71/20.95          | ~ (l1_pre_topc @ X40))),
% 20.71/20.95      inference('cnf', [status(esa)], [zf_stmt_13])).
% 20.71/20.95  thf('16', plain,
% 20.71/20.95      (![X0 : $i]: ((zip_tseitin_5 @ X0 @ sk_A) | ~ (v2_pre_topc @ sk_A))),
% 20.71/20.95      inference('sup-', [status(thm)], ['14', '15'])).
% 20.71/20.95  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 20.71/20.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.71/20.95  thf('18', plain, (![X0 : $i]: (zip_tseitin_5 @ X0 @ sk_A)),
% 20.71/20.95      inference('demod', [status(thm)], ['16', '17'])).
% 20.71/20.95  thf('19', plain,
% 20.71/20.95      (![X43 : $i]:
% 20.71/20.95         ((m1_subset_1 @ (u1_pre_topc @ X43) @ 
% 20.71/20.95           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X43))))
% 20.71/20.95          | ~ (l1_pre_topc @ X43))),
% 20.71/20.95      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 20.71/20.95  thf('20', plain,
% 20.71/20.95      (![X37 : $i, X38 : $i]:
% 20.71/20.95         (~ (m1_subset_1 @ X37 @ 
% 20.71/20.95             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38))))
% 20.71/20.95          | (zip_tseitin_4 @ X37 @ X38)
% 20.71/20.95          | ~ (zip_tseitin_5 @ X37 @ X38))),
% 20.71/20.95      inference('cnf', [status(esa)], [zf_stmt_2])).
% 20.71/20.95  thf('21', plain,
% 20.71/20.95      (![X0 : $i]:
% 20.71/20.95         (~ (l1_pre_topc @ X0)
% 20.71/20.95          | ~ (zip_tseitin_5 @ (u1_pre_topc @ X0) @ X0)
% 20.71/20.95          | (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0))),
% 20.71/20.95      inference('sup-', [status(thm)], ['19', '20'])).
% 20.71/20.95  thf('22', plain,
% 20.71/20.95      (((zip_tseitin_4 @ (u1_pre_topc @ sk_A) @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 20.71/20.95      inference('sup-', [status(thm)], ['18', '21'])).
% 20.71/20.95  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 20.71/20.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.71/20.95  thf('24', plain, ((zip_tseitin_4 @ (u1_pre_topc @ sk_A) @ sk_A)),
% 20.71/20.95      inference('demod', [status(thm)], ['22', '23'])).
% 20.71/20.95  thf(d10_xboole_0, axiom,
% 20.71/20.95    (![A:$i,B:$i]:
% 20.71/20.95     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 20.71/20.95  thf('25', plain,
% 20.71/20.95      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 20.71/20.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 20.71/20.95  thf('26', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 20.71/20.95      inference('simplify', [status(thm)], ['25'])).
% 20.71/20.95  thf('27', plain,
% 20.71/20.95      (![X34 : $i, X35 : $i]:
% 20.71/20.95         (~ (r1_tarski @ X34 @ (u1_pre_topc @ X35))
% 20.71/20.95          | (r2_hidden @ (k5_setfam_1 @ (u1_struct_0 @ X35) @ X34) @ 
% 20.71/20.95             (u1_pre_topc @ X35))
% 20.71/20.95          | ~ (zip_tseitin_4 @ X34 @ X35))),
% 20.71/20.95      inference('cnf', [status(esa)], [zf_stmt_4])).
% 20.71/20.95  thf('28', plain,
% 20.71/20.95      (![X0 : $i]:
% 20.71/20.95         (~ (zip_tseitin_4 @ (u1_pre_topc @ X0) @ X0)
% 20.71/20.95          | (r2_hidden @ 
% 20.71/20.95             (k5_setfam_1 @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 20.71/20.95             (u1_pre_topc @ X0)))),
% 20.71/20.95      inference('sup-', [status(thm)], ['26', '27'])).
% 20.71/20.95  thf('29', plain,
% 20.71/20.95      ((r2_hidden @ 
% 20.71/20.95        (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 20.71/20.95        (u1_pre_topc @ sk_A))),
% 20.71/20.95      inference('sup-', [status(thm)], ['24', '28'])).
% 20.71/20.95  thf('30', plain,
% 20.71/20.95      (![X40 : $i]:
% 20.71/20.95         (~ (v2_pre_topc @ X40)
% 20.71/20.95          | (r2_hidden @ (u1_struct_0 @ X40) @ (u1_pre_topc @ X40))
% 20.71/20.95          | ~ (l1_pre_topc @ X40))),
% 20.71/20.95      inference('cnf', [status(esa)], [zf_stmt_13])).
% 20.71/20.95  thf('31', plain,
% 20.71/20.95      (![X18 : $i, X20 : $i, X21 : $i]:
% 20.71/20.95         ((zip_tseitin_0 @ X20 @ X18 @ X21)
% 20.71/20.95          | ~ (r2_hidden @ X20 @ (u1_pre_topc @ X21))
% 20.71/20.95          | ~ (r2_hidden @ X18 @ (u1_pre_topc @ X21)))),
% 20.71/20.95      inference('cnf', [status(esa)], [zf_stmt_12])).
% 20.71/20.95  thf('32', plain,
% 20.71/20.95      (![X0 : $i, X1 : $i]:
% 20.71/20.95         (~ (l1_pre_topc @ X0)
% 20.71/20.95          | ~ (v2_pre_topc @ X0)
% 20.71/20.95          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0))
% 20.71/20.95          | (zip_tseitin_0 @ (u1_struct_0 @ X0) @ X1 @ X0))),
% 20.71/20.95      inference('sup-', [status(thm)], ['30', '31'])).
% 20.71/20.95  thf('33', plain,
% 20.71/20.95      (((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 20.71/20.95         (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_A)
% 20.71/20.95        | ~ (v2_pre_topc @ sk_A)
% 20.71/20.95        | ~ (l1_pre_topc @ sk_A))),
% 20.71/20.95      inference('sup-', [status(thm)], ['29', '32'])).
% 20.71/20.95  thf('34', plain, ((v2_pre_topc @ sk_A)),
% 20.71/20.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.71/20.95  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 20.71/20.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.71/20.95  thf('36', plain,
% 20.71/20.95      ((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 20.71/20.95        (k5_setfam_1 @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_A)),
% 20.71/20.95      inference('demod', [status(thm)], ['33', '34', '35'])).
% 20.71/20.95  thf('37', plain,
% 20.71/20.95      (![X18 : $i, X19 : $i, X20 : $i]:
% 20.71/20.95         ((r2_hidden @ X20 @ (u1_pre_topc @ X19))
% 20.71/20.95          | ~ (zip_tseitin_0 @ X20 @ X18 @ X19))),
% 20.71/20.95      inference('cnf', [status(esa)], [zf_stmt_12])).
% 20.71/20.95  thf('38', plain, ((r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))),
% 20.71/20.95      inference('sup-', [status(thm)], ['36', '37'])).
% 20.71/20.95  thf('39', plain,
% 20.71/20.95      (![X10 : $i, X11 : $i]:
% 20.71/20.95         ((r1_tarski @ X10 @ (k3_tarski @ X11)) | ~ (r2_hidden @ X10 @ X11))),
% 20.71/20.95      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 20.71/20.95  thf('40', plain,
% 20.71/20.95      ((r1_tarski @ (u1_struct_0 @ sk_A) @ (k3_tarski @ (u1_pre_topc @ sk_A)))),
% 20.71/20.95      inference('sup-', [status(thm)], ['38', '39'])).
% 20.71/20.95  thf('41', plain,
% 20.71/20.95      (![X7 : $i, X9 : $i]:
% 20.71/20.95         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 20.71/20.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 20.71/20.95  thf('42', plain,
% 20.71/20.95      ((~ (r1_tarski @ (k3_tarski @ (u1_pre_topc @ sk_A)) @ 
% 20.71/20.95           (u1_struct_0 @ sk_A))
% 20.71/20.95        | ((k3_tarski @ (u1_pre_topc @ sk_A)) = (u1_struct_0 @ sk_A)))),
% 20.71/20.95      inference('sup-', [status(thm)], ['40', '41'])).
% 20.71/20.95  thf('43', plain,
% 20.71/20.95      ((~ (l1_pre_topc @ sk_A)
% 20.71/20.95        | ((k3_tarski @ (u1_pre_topc @ sk_A)) = (u1_struct_0 @ sk_A)))),
% 20.71/20.95      inference('sup-', [status(thm)], ['13', '42'])).
% 20.71/20.95  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 20.71/20.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.71/20.95  thf('45', plain,
% 20.71/20.95      (((k3_tarski @ (u1_pre_topc @ sk_A)) = (u1_struct_0 @ sk_A))),
% 20.71/20.95      inference('demod', [status(thm)], ['43', '44'])).
% 20.71/20.95  thf(t14_yellow_1, axiom,
% 20.71/20.95    (![A:$i]:
% 20.71/20.95     ( ( ~( v1_xboole_0 @ A ) ) =>
% 20.71/20.95       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 20.71/20.95         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 20.71/20.95  thf('46', plain,
% 20.71/20.95      (![X44 : $i]:
% 20.71/20.95         (~ (r2_hidden @ (k3_tarski @ X44) @ X44)
% 20.71/20.95          | ((k4_yellow_0 @ (k2_yellow_1 @ X44)) = (k3_tarski @ X44))
% 20.71/20.95          | (v1_xboole_0 @ X44))),
% 20.71/20.95      inference('cnf', [status(esa)], [t14_yellow_1])).
% 20.71/20.95  thf(d1_xboole_0, axiom,
% 20.71/20.95    (![A:$i]:
% 20.71/20.95     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 20.71/20.95  thf('47', plain,
% 20.71/20.95      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 20.71/20.95      inference('cnf', [status(esa)], [d1_xboole_0])).
% 20.71/20.95  thf('48', plain,
% 20.71/20.95      (![X44 : $i]:
% 20.71/20.95         (((k4_yellow_0 @ (k2_yellow_1 @ X44)) = (k3_tarski @ X44))
% 20.71/20.95          | ~ (r2_hidden @ (k3_tarski @ X44) @ X44))),
% 20.71/20.95      inference('clc', [status(thm)], ['46', '47'])).
% 20.71/20.95  thf('49', plain,
% 20.71/20.95      ((~ (r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 20.71/20.95        | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 20.71/20.95            = (k3_tarski @ (u1_pre_topc @ sk_A))))),
% 20.71/20.95      inference('sup-', [status(thm)], ['45', '48'])).
% 20.71/20.95  thf('50', plain, ((r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))),
% 20.71/20.95      inference('sup-', [status(thm)], ['36', '37'])).
% 20.71/20.95  thf('51', plain,
% 20.71/20.95      (((k3_tarski @ (u1_pre_topc @ sk_A)) = (u1_struct_0 @ sk_A))),
% 20.71/20.95      inference('demod', [status(thm)], ['43', '44'])).
% 20.71/20.95  thf('52', plain,
% 20.71/20.95      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 20.71/20.95         = (u1_struct_0 @ sk_A))),
% 20.71/20.95      inference('demod', [status(thm)], ['49', '50', '51'])).
% 20.71/20.95  thf('53', plain,
% 20.71/20.95      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 20.71/20.95         != (u1_struct_0 @ sk_A))),
% 20.71/20.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.71/20.95  thf('54', plain, ($false),
% 20.71/20.95      inference('simplify_reflect-', [status(thm)], ['52', '53'])).
% 20.71/20.95  
% 20.71/20.95  % SZS output end Refutation
% 20.71/20.95  
% 20.71/20.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
