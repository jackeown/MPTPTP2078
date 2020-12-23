%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OjBh1R5jjZ

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:22 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 293 expanded)
%              Number of leaves         :   46 ( 111 expanded)
%              Depth                    :   18
%              Number of atoms          :  748 (2605 expanded)
%              Number of equality atoms :   15 (  70 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(k4_yellow_0_type,type,(
    k4_yellow_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X8 ) @ X9 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X41: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X41 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X41 ) ) ) )
      | ~ ( l1_pre_topc @ X41 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( m1_subset_1 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ( m1_subset_1 @ ( sk_C @ X1 @ ( u1_pre_topc @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( sk_C @ X1 @ ( u1_pre_topc @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X8 ) @ X9 )
      | ~ ( r1_tarski @ ( sk_C @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

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

thf('10',plain,(
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

thf('11',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v2_pre_topc @ X38 )
      | ( zip_tseitin_3 @ X39 @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( zip_tseitin_3 @ X0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( zip_tseitin_2 @ X30 @ X28 @ X29 )
      | ~ ( zip_tseitin_3 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( zip_tseitin_2 @ X1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( zip_tseitin_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('23',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( zip_tseitin_1 @ X24 @ X26 @ X25 )
      | ~ ( zip_tseitin_2 @ X24 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_2 @ ( u1_struct_0 @ X0 ) @ X1 @ X0 )
      | ( zip_tseitin_1 @ ( u1_struct_0 @ X0 ) @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    zip_tseitin_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X38: $i] :
      ( ~ ( v2_pre_topc @ X38 )
      | ( r2_hidden @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('27',plain,(
    ! [X38: $i] :
      ( ~ ( v2_pre_topc @ X38 )
      | ( r2_hidden @ ( u1_struct_0 @ X38 ) @ ( u1_pre_topc @ X38 ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('28',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X16 @ X19 )
      | ~ ( r2_hidden @ X18 @ ( u1_pre_topc @ X19 ) )
      | ~ ( r2_hidden @ X16 @ ( u1_pre_topc @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ X0 ) @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 @ X20 ) @ ( u1_pre_topc @ X22 ) )
      | ~ ( zip_tseitin_1 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( zip_tseitin_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ X0 )
      | ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) )
      | ( zip_tseitin_0 @ ( u1_struct_0 @ X0 ) @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('39',plain,
    ( ( zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    zip_tseitin_0 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X18 @ ( u1_pre_topc @ X17 ) )
      | ~ ( zip_tseitin_0 @ X18 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_12])).

thf('44',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('45',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ ( k3_tarski @ X7 ) )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('46',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('48',plain,
    ( ~ ( r1_tarski @ ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t14_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ ( k3_tarski @ A ) @ A )
       => ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) )
          = ( k3_tarski @ A ) ) ) ) )).

thf('52',plain,(
    ! [X42: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ X42 ) @ X42 )
      | ( ( k4_yellow_0 @ ( k2_yellow_1 @ X42 ) )
        = ( k3_tarski @ X42 ) )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('54',plain,(
    ! [X42: $i] :
      ( ( ( k4_yellow_0 @ ( k2_yellow_1 @ X42 ) )
        = ( k3_tarski @ X42 ) )
      | ~ ( r2_hidden @ ( k3_tarski @ X42 ) @ X42 ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    | ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
      = ( k3_tarski @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('57',plain,
    ( ( k3_tarski @ ( u1_pre_topc @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('58',plain,
    ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OjBh1R5jjZ
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:06:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.99/1.23  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.99/1.23  % Solved by: fo/fo7.sh
% 0.99/1.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.23  % done 1330 iterations in 0.777s
% 0.99/1.23  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.99/1.23  % SZS output start Refutation
% 0.99/1.23  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.99/1.23  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.99/1.23  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.99/1.23  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.99/1.23  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.99/1.23  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.99/1.23  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.99/1.23  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.99/1.23  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.99/1.23  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.99/1.23  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.99/1.23  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.23  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.99/1.23  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.99/1.23  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $o).
% 0.99/1.23  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.99/1.23  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.99/1.23  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.99/1.23  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.99/1.23  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.99/1.23  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.99/1.23  thf(k4_yellow_0_type, type, k4_yellow_0: $i > $i).
% 0.99/1.23  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.99/1.23  thf(t94_zfmisc_1, axiom,
% 0.99/1.23    (![A:$i,B:$i]:
% 0.99/1.23     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 0.99/1.23       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 0.99/1.23  thf('0', plain,
% 0.99/1.23      (![X8 : $i, X9 : $i]:
% 0.99/1.23         ((r1_tarski @ (k3_tarski @ X8) @ X9)
% 0.99/1.23          | (r2_hidden @ (sk_C @ X9 @ X8) @ X8))),
% 0.99/1.23      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.99/1.23  thf(dt_u1_pre_topc, axiom,
% 0.99/1.23    (![A:$i]:
% 0.99/1.23     ( ( l1_pre_topc @ A ) =>
% 0.99/1.23       ( m1_subset_1 @
% 0.99/1.23         ( u1_pre_topc @ A ) @ 
% 0.99/1.23         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.99/1.23  thf('1', plain,
% 0.99/1.23      (![X41 : $i]:
% 0.99/1.23         ((m1_subset_1 @ (u1_pre_topc @ X41) @ 
% 0.99/1.23           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X41))))
% 0.99/1.23          | ~ (l1_pre_topc @ X41))),
% 0.99/1.23      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.99/1.23  thf(t4_subset, axiom,
% 0.99/1.23    (![A:$i,B:$i,C:$i]:
% 0.99/1.23     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.99/1.23       ( m1_subset_1 @ A @ C ) ))).
% 0.99/1.23  thf('2', plain,
% 0.99/1.23      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.99/1.23         (~ (r2_hidden @ X13 @ X14)
% 0.99/1.23          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.99/1.23          | (m1_subset_1 @ X13 @ X15))),
% 0.99/1.23      inference('cnf', [status(esa)], [t4_subset])).
% 0.99/1.23  thf('3', plain,
% 0.99/1.23      (![X0 : $i, X1 : $i]:
% 0.99/1.23         (~ (l1_pre_topc @ X0)
% 0.99/1.23          | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.99/1.23          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0)))),
% 0.99/1.23      inference('sup-', [status(thm)], ['1', '2'])).
% 0.99/1.23  thf('4', plain,
% 0.99/1.23      (![X0 : $i, X1 : $i]:
% 0.99/1.23         ((r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ X1)
% 0.99/1.23          | (m1_subset_1 @ (sk_C @ X1 @ (u1_pre_topc @ X0)) @ 
% 0.99/1.23             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.99/1.23          | ~ (l1_pre_topc @ X0))),
% 0.99/1.23      inference('sup-', [status(thm)], ['0', '3'])).
% 0.99/1.23  thf(t3_subset, axiom,
% 0.99/1.23    (![A:$i,B:$i]:
% 0.99/1.23     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.99/1.23  thf('5', plain,
% 0.99/1.23      (![X10 : $i, X11 : $i]:
% 0.99/1.23         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.99/1.23      inference('cnf', [status(esa)], [t3_subset])).
% 0.99/1.23  thf('6', plain,
% 0.99/1.23      (![X0 : $i, X1 : $i]:
% 0.99/1.23         (~ (l1_pre_topc @ X0)
% 0.99/1.23          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ X1)
% 0.99/1.23          | (r1_tarski @ (sk_C @ X1 @ (u1_pre_topc @ X0)) @ (u1_struct_0 @ X0)))),
% 0.99/1.23      inference('sup-', [status(thm)], ['4', '5'])).
% 0.99/1.23  thf('7', plain,
% 0.99/1.23      (![X8 : $i, X9 : $i]:
% 0.99/1.23         ((r1_tarski @ (k3_tarski @ X8) @ X9)
% 0.99/1.23          | ~ (r1_tarski @ (sk_C @ X9 @ X8) @ X9))),
% 0.99/1.23      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.99/1.23  thf('8', plain,
% 0.99/1.23      (![X0 : $i]:
% 0.99/1.23         ((r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_struct_0 @ X0))
% 0.99/1.23          | ~ (l1_pre_topc @ X0)
% 0.99/1.23          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_struct_0 @ X0)))),
% 0.99/1.23      inference('sup-', [status(thm)], ['6', '7'])).
% 0.99/1.23  thf('9', plain,
% 0.99/1.23      (![X0 : $i]:
% 0.99/1.23         (~ (l1_pre_topc @ X0)
% 0.99/1.23          | (r1_tarski @ (k3_tarski @ (u1_pre_topc @ X0)) @ (u1_struct_0 @ X0)))),
% 0.99/1.23      inference('simplify', [status(thm)], ['8'])).
% 0.99/1.23  thf(t24_yellow_1, conjecture,
% 0.99/1.23    (![A:$i]:
% 0.99/1.23     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.99/1.23       ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.99/1.23         ( u1_struct_0 @ A ) ) ))).
% 0.99/1.23  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.23    (~( ![A:$i]:
% 0.99/1.23        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.99/1.23            ( l1_pre_topc @ A ) ) =>
% 0.99/1.23          ( ( k4_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) ) =
% 0.99/1.23            ( u1_struct_0 @ A ) ) ) )),
% 0.99/1.23    inference('cnf.neg', [status(esa)], [t24_yellow_1])).
% 0.99/1.23  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.23  thf(d1_pre_topc, axiom,
% 0.99/1.23    (![A:$i]:
% 0.99/1.23     ( ( l1_pre_topc @ A ) =>
% 0.99/1.23       ( ( v2_pre_topc @ A ) <=>
% 0.99/1.23         ( ( ![B:$i]:
% 0.99/1.23             ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.23               ( ![C:$i]:
% 0.99/1.23                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.23                   ( ( ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) & 
% 0.99/1.23                       ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) =>
% 0.99/1.23                     ( r2_hidden @
% 0.99/1.23                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.99/1.23                       ( u1_pre_topc @ A ) ) ) ) ) ) ) & 
% 0.99/1.23           ( ![B:$i]:
% 0.99/1.23             ( ( m1_subset_1 @
% 0.99/1.23                 B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.23               ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.99/1.23                 ( r2_hidden @
% 0.99/1.23                   ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.99/1.23                   ( u1_pre_topc @ A ) ) ) ) ) & 
% 0.99/1.23           ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.99/1.23  thf(zf_stmt_1, type, zip_tseitin_5 : $i > $i > $o).
% 0.99/1.23  thf(zf_stmt_2, axiom,
% 0.99/1.23    (![B:$i,A:$i]:
% 0.99/1.23     ( ( zip_tseitin_5 @ B @ A ) <=>
% 0.99/1.23       ( ( m1_subset_1 @
% 0.99/1.23           B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.23         ( zip_tseitin_4 @ B @ A ) ) ))).
% 0.99/1.23  thf(zf_stmt_3, type, zip_tseitin_4 : $i > $i > $o).
% 0.99/1.23  thf(zf_stmt_4, axiom,
% 0.99/1.23    (![B:$i,A:$i]:
% 0.99/1.23     ( ( zip_tseitin_4 @ B @ A ) <=>
% 0.99/1.23       ( ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) =>
% 0.99/1.23         ( r2_hidden @
% 0.99/1.23           ( k5_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.99/1.23  thf(zf_stmt_5, type, zip_tseitin_3 : $i > $i > $o).
% 0.99/1.23  thf(zf_stmt_6, axiom,
% 0.99/1.23    (![B:$i,A:$i]:
% 0.99/1.23     ( ( zip_tseitin_3 @ B @ A ) <=>
% 0.99/1.23       ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.23         ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.99/1.23  thf(zf_stmt_7, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.99/1.23  thf(zf_stmt_8, axiom,
% 0.99/1.23    (![C:$i,B:$i,A:$i]:
% 0.99/1.23     ( ( zip_tseitin_2 @ C @ B @ A ) <=>
% 0.99/1.23       ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.23         ( zip_tseitin_1 @ C @ B @ A ) ) ))).
% 0.99/1.23  thf(zf_stmt_9, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.99/1.23  thf(zf_stmt_10, axiom,
% 0.99/1.23    (![C:$i,B:$i,A:$i]:
% 0.99/1.23     ( ( zip_tseitin_1 @ C @ B @ A ) <=>
% 0.99/1.23       ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.99/1.23         ( r2_hidden @
% 0.99/1.23           ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( u1_pre_topc @ A ) ) ) ))).
% 0.99/1.23  thf(zf_stmt_11, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.99/1.23  thf(zf_stmt_12, axiom,
% 0.99/1.23    (![C:$i,B:$i,A:$i]:
% 0.99/1.23     ( ( zip_tseitin_0 @ C @ B @ A ) <=>
% 0.99/1.23       ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) & 
% 0.99/1.23         ( r2_hidden @ C @ ( u1_pre_topc @ A ) ) ) ))).
% 0.99/1.23  thf(zf_stmt_13, axiom,
% 0.99/1.23    (![A:$i]:
% 0.99/1.23     ( ( l1_pre_topc @ A ) =>
% 0.99/1.23       ( ( v2_pre_topc @ A ) <=>
% 0.99/1.23         ( ( r2_hidden @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) & 
% 0.99/1.23           ( ![B:$i]: ( zip_tseitin_5 @ B @ A ) ) & 
% 0.99/1.23           ( ![B:$i]: ( zip_tseitin_3 @ B @ A ) ) ) ) ))).
% 0.99/1.23  thf('11', plain,
% 0.99/1.23      (![X38 : $i, X39 : $i]:
% 0.99/1.23         (~ (v2_pre_topc @ X38)
% 0.99/1.23          | (zip_tseitin_3 @ X39 @ X38)
% 0.99/1.23          | ~ (l1_pre_topc @ X38))),
% 0.99/1.23      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.99/1.23  thf('12', plain,
% 0.99/1.23      (![X0 : $i]: ((zip_tseitin_3 @ X0 @ sk_A) | ~ (v2_pre_topc @ sk_A))),
% 0.99/1.23      inference('sup-', [status(thm)], ['10', '11'])).
% 0.99/1.23  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.23  thf('14', plain, (![X0 : $i]: (zip_tseitin_3 @ X0 @ sk_A)),
% 0.99/1.23      inference('demod', [status(thm)], ['12', '13'])).
% 0.99/1.23  thf(d10_xboole_0, axiom,
% 0.99/1.23    (![A:$i,B:$i]:
% 0.99/1.23     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.99/1.23  thf('15', plain,
% 0.99/1.23      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.99/1.23      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.99/1.23  thf('16', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.99/1.23      inference('simplify', [status(thm)], ['15'])).
% 0.99/1.23  thf('17', plain,
% 0.99/1.23      (![X10 : $i, X12 : $i]:
% 0.99/1.23         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.99/1.23      inference('cnf', [status(esa)], [t3_subset])).
% 0.99/1.23  thf('18', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.99/1.23      inference('sup-', [status(thm)], ['16', '17'])).
% 0.99/1.23  thf('19', plain,
% 0.99/1.23      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.99/1.23         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.99/1.23          | (zip_tseitin_2 @ X30 @ X28 @ X29)
% 0.99/1.23          | ~ (zip_tseitin_3 @ X28 @ X29))),
% 0.99/1.23      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.99/1.23  thf('20', plain,
% 0.99/1.23      (![X0 : $i, X1 : $i]:
% 0.99/1.23         (~ (zip_tseitin_3 @ (u1_struct_0 @ X0) @ X0)
% 0.99/1.23          | (zip_tseitin_2 @ X1 @ (u1_struct_0 @ X0) @ X0))),
% 0.99/1.23      inference('sup-', [status(thm)], ['18', '19'])).
% 0.99/1.23  thf('21', plain,
% 0.99/1.23      (![X0 : $i]: (zip_tseitin_2 @ X0 @ (u1_struct_0 @ sk_A) @ sk_A)),
% 0.99/1.23      inference('sup-', [status(thm)], ['14', '20'])).
% 0.99/1.23  thf('22', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.99/1.23      inference('sup-', [status(thm)], ['16', '17'])).
% 0.99/1.23  thf('23', plain,
% 0.99/1.23      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.99/1.23         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.99/1.23          | (zip_tseitin_1 @ X24 @ X26 @ X25)
% 0.99/1.23          | ~ (zip_tseitin_2 @ X24 @ X26 @ X25))),
% 0.99/1.23      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.99/1.23  thf('24', plain,
% 0.99/1.23      (![X0 : $i, X1 : $i]:
% 0.99/1.23         (~ (zip_tseitin_2 @ (u1_struct_0 @ X0) @ X1 @ X0)
% 0.99/1.23          | (zip_tseitin_1 @ (u1_struct_0 @ X0) @ X1 @ X0))),
% 0.99/1.23      inference('sup-', [status(thm)], ['22', '23'])).
% 0.99/1.23  thf('25', plain,
% 0.99/1.23      ((zip_tseitin_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_A)),
% 0.99/1.23      inference('sup-', [status(thm)], ['21', '24'])).
% 0.99/1.23  thf('26', plain,
% 0.99/1.23      (![X38 : $i]:
% 0.99/1.23         (~ (v2_pre_topc @ X38)
% 0.99/1.23          | (r2_hidden @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38))
% 0.99/1.23          | ~ (l1_pre_topc @ X38))),
% 0.99/1.23      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.99/1.23  thf('27', plain,
% 0.99/1.23      (![X38 : $i]:
% 0.99/1.23         (~ (v2_pre_topc @ X38)
% 0.99/1.23          | (r2_hidden @ (u1_struct_0 @ X38) @ (u1_pre_topc @ X38))
% 0.99/1.23          | ~ (l1_pre_topc @ X38))),
% 0.99/1.23      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.99/1.23  thf('28', plain,
% 0.99/1.23      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.99/1.23         ((zip_tseitin_0 @ X18 @ X16 @ X19)
% 0.99/1.23          | ~ (r2_hidden @ X18 @ (u1_pre_topc @ X19))
% 0.99/1.23          | ~ (r2_hidden @ X16 @ (u1_pre_topc @ X19)))),
% 0.99/1.23      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.99/1.23  thf('29', plain,
% 0.99/1.23      (![X0 : $i, X1 : $i]:
% 0.99/1.23         (~ (l1_pre_topc @ X0)
% 0.99/1.23          | ~ (v2_pre_topc @ X0)
% 0.99/1.23          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0))
% 0.99/1.23          | (zip_tseitin_0 @ (u1_struct_0 @ X0) @ X1 @ X0))),
% 0.99/1.23      inference('sup-', [status(thm)], ['27', '28'])).
% 0.99/1.23  thf('30', plain,
% 0.99/1.23      (![X0 : $i]:
% 0.99/1.23         (~ (l1_pre_topc @ X0)
% 0.99/1.23          | ~ (v2_pre_topc @ X0)
% 0.99/1.23          | (zip_tseitin_0 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0)
% 0.99/1.23          | ~ (v2_pre_topc @ X0)
% 0.99/1.23          | ~ (l1_pre_topc @ X0))),
% 0.99/1.23      inference('sup-', [status(thm)], ['26', '29'])).
% 0.99/1.23  thf('31', plain,
% 0.99/1.23      (![X0 : $i]:
% 0.99/1.23         ((zip_tseitin_0 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0)
% 0.99/1.23          | ~ (v2_pre_topc @ X0)
% 0.99/1.23          | ~ (l1_pre_topc @ X0))),
% 0.99/1.23      inference('simplify', [status(thm)], ['30'])).
% 0.99/1.23  thf('32', plain,
% 0.99/1.23      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.99/1.23         (~ (zip_tseitin_0 @ X20 @ X21 @ X22)
% 0.99/1.23          | (r2_hidden @ (k9_subset_1 @ (u1_struct_0 @ X22) @ X21 @ X20) @ 
% 0.99/1.23             (u1_pre_topc @ X22))
% 0.99/1.23          | ~ (zip_tseitin_1 @ X20 @ X21 @ X22))),
% 0.99/1.23      inference('cnf', [status(esa)], [zf_stmt_10])).
% 0.99/1.23  thf('33', plain,
% 0.99/1.23      (![X0 : $i]:
% 0.99/1.23         (~ (l1_pre_topc @ X0)
% 0.99/1.23          | ~ (v2_pre_topc @ X0)
% 0.99/1.23          | ~ (zip_tseitin_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ X0)
% 0.99/1.23          | (r2_hidden @ 
% 0.99/1.23             (k9_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 0.99/1.23              (u1_struct_0 @ X0)) @ 
% 0.99/1.23             (u1_pre_topc @ X0)))),
% 0.99/1.23      inference('sup-', [status(thm)], ['31', '32'])).
% 0.99/1.23  thf('34', plain,
% 0.99/1.23      (((r2_hidden @ 
% 0.99/1.23         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.23          (u1_struct_0 @ sk_A)) @ 
% 0.99/1.23         (u1_pre_topc @ sk_A))
% 0.99/1.23        | ~ (v2_pre_topc @ sk_A)
% 0.99/1.23        | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.23      inference('sup-', [status(thm)], ['25', '33'])).
% 0.99/1.23  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.23  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.23  thf('37', plain,
% 0.99/1.23      ((r2_hidden @ 
% 0.99/1.23        (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.23         (u1_struct_0 @ sk_A)) @ 
% 0.99/1.23        (u1_pre_topc @ sk_A))),
% 0.99/1.23      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.99/1.23  thf('38', plain,
% 0.99/1.23      (![X0 : $i, X1 : $i]:
% 0.99/1.23         (~ (l1_pre_topc @ X0)
% 0.99/1.23          | ~ (v2_pre_topc @ X0)
% 0.99/1.23          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0))
% 0.99/1.23          | (zip_tseitin_0 @ (u1_struct_0 @ X0) @ X1 @ X0))),
% 0.99/1.23      inference('sup-', [status(thm)], ['27', '28'])).
% 0.99/1.23  thf('39', plain,
% 0.99/1.23      (((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.23         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.23          (u1_struct_0 @ sk_A)) @ 
% 0.99/1.23         sk_A)
% 0.99/1.23        | ~ (v2_pre_topc @ sk_A)
% 0.99/1.23        | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.23      inference('sup-', [status(thm)], ['37', '38'])).
% 0.99/1.23  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.23  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.23  thf('42', plain,
% 0.99/1.23      ((zip_tseitin_0 @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.23        (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.23         (u1_struct_0 @ sk_A)) @ 
% 0.99/1.23        sk_A)),
% 0.99/1.23      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.99/1.23  thf('43', plain,
% 0.99/1.23      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.99/1.23         ((r2_hidden @ X18 @ (u1_pre_topc @ X17))
% 0.99/1.23          | ~ (zip_tseitin_0 @ X18 @ X16 @ X17))),
% 0.99/1.23      inference('cnf', [status(esa)], [zf_stmt_12])).
% 0.99/1.23  thf('44', plain, ((r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))),
% 0.99/1.23      inference('sup-', [status(thm)], ['42', '43'])).
% 0.99/1.23  thf(l49_zfmisc_1, axiom,
% 0.99/1.23    (![A:$i,B:$i]:
% 0.99/1.23     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.99/1.23  thf('45', plain,
% 0.99/1.23      (![X6 : $i, X7 : $i]:
% 0.99/1.23         ((r1_tarski @ X6 @ (k3_tarski @ X7)) | ~ (r2_hidden @ X6 @ X7))),
% 0.99/1.23      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.99/1.23  thf('46', plain,
% 0.99/1.23      ((r1_tarski @ (u1_struct_0 @ sk_A) @ (k3_tarski @ (u1_pre_topc @ sk_A)))),
% 0.99/1.23      inference('sup-', [status(thm)], ['44', '45'])).
% 0.99/1.23  thf('47', plain,
% 0.99/1.23      (![X3 : $i, X5 : $i]:
% 0.99/1.23         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.99/1.23      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.99/1.23  thf('48', plain,
% 0.99/1.23      ((~ (r1_tarski @ (k3_tarski @ (u1_pre_topc @ sk_A)) @ 
% 0.99/1.23           (u1_struct_0 @ sk_A))
% 0.99/1.23        | ((k3_tarski @ (u1_pre_topc @ sk_A)) = (u1_struct_0 @ sk_A)))),
% 0.99/1.23      inference('sup-', [status(thm)], ['46', '47'])).
% 0.99/1.23  thf('49', plain,
% 0.99/1.23      ((~ (l1_pre_topc @ sk_A)
% 0.99/1.23        | ((k3_tarski @ (u1_pre_topc @ sk_A)) = (u1_struct_0 @ sk_A)))),
% 0.99/1.23      inference('sup-', [status(thm)], ['9', '48'])).
% 0.99/1.23  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.23  thf('51', plain,
% 0.99/1.23      (((k3_tarski @ (u1_pre_topc @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.99/1.23      inference('demod', [status(thm)], ['49', '50'])).
% 0.99/1.23  thf(t14_yellow_1, axiom,
% 0.99/1.23    (![A:$i]:
% 0.99/1.23     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.99/1.23       ( ( r2_hidden @ ( k3_tarski @ A ) @ A ) =>
% 0.99/1.23         ( ( k4_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k3_tarski @ A ) ) ) ))).
% 0.99/1.23  thf('52', plain,
% 0.99/1.23      (![X42 : $i]:
% 0.99/1.23         (~ (r2_hidden @ (k3_tarski @ X42) @ X42)
% 0.99/1.23          | ((k4_yellow_0 @ (k2_yellow_1 @ X42)) = (k3_tarski @ X42))
% 0.99/1.23          | (v1_xboole_0 @ X42))),
% 0.99/1.23      inference('cnf', [status(esa)], [t14_yellow_1])).
% 0.99/1.23  thf(d1_xboole_0, axiom,
% 0.99/1.23    (![A:$i]:
% 0.99/1.23     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.99/1.23  thf('53', plain,
% 0.99/1.23      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.99/1.23      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.99/1.23  thf('54', plain,
% 0.99/1.23      (![X42 : $i]:
% 0.99/1.23         (((k4_yellow_0 @ (k2_yellow_1 @ X42)) = (k3_tarski @ X42))
% 0.99/1.23          | ~ (r2_hidden @ (k3_tarski @ X42) @ X42))),
% 0.99/1.23      inference('clc', [status(thm)], ['52', '53'])).
% 0.99/1.23  thf('55', plain,
% 0.99/1.23      ((~ (r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.99/1.23        | ((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 0.99/1.23            = (k3_tarski @ (u1_pre_topc @ sk_A))))),
% 0.99/1.23      inference('sup-', [status(thm)], ['51', '54'])).
% 0.99/1.23  thf('56', plain, ((r2_hidden @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))),
% 0.99/1.23      inference('sup-', [status(thm)], ['42', '43'])).
% 0.99/1.23  thf('57', plain,
% 0.99/1.23      (((k3_tarski @ (u1_pre_topc @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.99/1.23      inference('demod', [status(thm)], ['49', '50'])).
% 0.99/1.23  thf('58', plain,
% 0.99/1.23      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 0.99/1.23         = (u1_struct_0 @ sk_A))),
% 0.99/1.23      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.99/1.23  thf('59', plain,
% 0.99/1.23      (((k4_yellow_0 @ (k2_yellow_1 @ (u1_pre_topc @ sk_A)))
% 0.99/1.23         != (u1_struct_0 @ sk_A))),
% 0.99/1.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.23  thf('60', plain, ($false),
% 0.99/1.23      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 0.99/1.23  
% 0.99/1.23  % SZS output end Refutation
% 0.99/1.23  
% 0.99/1.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
