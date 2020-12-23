%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bLlOz2Gjvf

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:03 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 307 expanded)
%              Number of leaves         :   43 ( 102 expanded)
%              Depth                    :   18
%              Number of atoms          : 1170 (3530 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t20_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A )
          <=> ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A )
            <=> ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_tex_2])).

thf('0',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ X42 )
      | ( v1_subset_1 @ ( k6_domain_1 @ X42 @ X41 ) @ X42 )
      | ( v1_zfmisc_1 @ X42 )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t7_tex_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(rc1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ? [B: $i] :
          ( ( v1_zfmisc_1 @ B )
          & ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X40: $i] :
      ( ( v1_zfmisc_1 @ ( sk_B_1 @ X40 ) )
      | ( v1_xboole_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[rc1_tex_2])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc5_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_zfmisc_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_zfmisc_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( v1_zfmisc_1 @ X22 )
      | ~ ( v1_zfmisc_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(fc7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ~ ( v1_xboole_0 @ ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ~ ( v1_xboole_0 @ ( k6_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc7_subset_1])).

thf('11',plain,(
    v1_zfmisc_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( v1_zfmisc_1 @ X22 )
      | ~ ( v1_zfmisc_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_zfmisc_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_zfmisc_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['4','19'])).

thf('21',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('22',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc6_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('23',plain,(
    ! [X27: $i] :
      ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 )
      | ( v7_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc6_struct_0])).

thf('24',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('26',plain,(
    ! [X24: $i] :
      ( ( l1_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('27',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v7_struct_0 @ sk_A )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) )
        & ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ) )).

thf('32',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( l1_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X36 @ X37 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('33',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference(clc,[status(thm)],['35','36'])).

thf(cc10_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v7_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ~ ( v2_struct_0 @ B )
           => ( ~ ( v2_struct_0 @ B )
              & ~ ( v1_tex_2 @ B @ A ) ) ) ) ) )).

thf('38',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( v1_tex_2 @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v7_struct_0 @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[cc10_tex_2])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
      | ~ ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( l1_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('45',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(clc,[status(thm)],['42','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','52'])).

thf('54',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(split,[status(esa)],['29'])).

thf('55',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference(clc,[status(thm)],['35','36'])).

thf(d3_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('56',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X31 @ X32 )
      | ( ( sk_C_1 @ X31 @ X32 )
        = ( u1_struct_0 @ X31 ) )
      | ( v1_tex_2 @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('57',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
    | ( ( sk_C_1 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
    | ( ( sk_C_1 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,
    ( ( ( sk_C_1 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference(clc,[status(thm)],['35','36'])).

thf('63',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X31 @ X32 )
      | ( m1_subset_1 @ ( sk_C_1 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( v1_tex_2 @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('64',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C_1 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['61','66'])).

thf('68',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('69',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(clc,[status(thm)],['67','68'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('70',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X35 = X34 )
      | ( v1_subset_1 @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('71',plain,
    ( ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( sk_C_1 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('73',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X31 @ X32 )
      | ~ ( v1_subset_1 @ ( sk_C_1 @ X31 @ X32 ) @ ( u1_struct_0 @ X32 ) )
      | ( v1_tex_2 @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('74',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference(clc,[status(thm)],['35','36'])).

thf('77',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('79',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(clc,[status(thm)],['71','79'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('81',plain,(
    ! [X28: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 )
      | ~ ( v7_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('82',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
      | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ) )).

thf('84',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( l1_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X38 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('85',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference(clc,[status(thm)],['35','36'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('91',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( l1_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('92',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X24: $i] :
      ( ( l1_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('96',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['82','89','96'])).

thf('98',plain,(
    ! [X27: $i] :
      ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 )
      | ( v7_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc6_struct_0])).

thf('99',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('101',plain,
    ( ( v7_struct_0 @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['29'])).

thf(t8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) )
              & ( v7_struct_0 @ A ) ) ) ) )).

thf('103',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( u1_struct_0 @ X44 ) )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X44 ) @ X43 ) @ ( u1_struct_0 @ X44 ) )
      | ~ ( v7_struct_0 @ X44 )
      | ~ ( l1_struct_0 @ X44 )
      | ( v2_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t8_tex_2])).

thf('104',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('106',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['101','109'])).

thf('111',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','53','54','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bLlOz2Gjvf
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:02:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.55  % Solved by: fo/fo7.sh
% 0.35/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.55  % done 171 iterations in 0.099s
% 0.35/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.55  % SZS output start Refutation
% 0.35/0.55  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.35/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.55  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.35/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.35/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.55  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.35/0.55  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.35/0.55  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.35/0.55  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.35/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.35/0.55  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.35/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.55  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.35/0.55  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.35/0.55  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.35/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.35/0.55  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.35/0.55                                           $i > $i).
% 0.35/0.55  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.35/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.55  thf(t20_tex_2, conjecture,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.55           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.35/0.55             ( v1_subset_1 @
% 0.35/0.55               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.35/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.55    (~( ![A:$i]:
% 0.35/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.55          ( ![B:$i]:
% 0.35/0.55            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.55              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.35/0.55                ( v1_subset_1 @
% 0.35/0.55                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.35/0.55                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.35/0.55    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.35/0.55  thf('0', plain,
% 0.35/0.55      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.35/0.55           (u1_struct_0 @ sk_A))
% 0.35/0.55        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('1', plain,
% 0.35/0.55      (~
% 0.35/0.55       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.35/0.55         (u1_struct_0 @ sk_A))) | 
% 0.35/0.55       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))),
% 0.35/0.55      inference('split', [status(esa)], ['0'])).
% 0.35/0.55  thf('2', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(t7_tex_2, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_zfmisc_1 @ A ) ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ A ) =>
% 0.35/0.55           ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) ))).
% 0.35/0.55  thf('3', plain,
% 0.35/0.55      (![X41 : $i, X42 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X41 @ X42)
% 0.35/0.55          | (v1_subset_1 @ (k6_domain_1 @ X42 @ X41) @ X42)
% 0.35/0.55          | (v1_zfmisc_1 @ X42)
% 0.35/0.55          | (v1_xboole_0 @ X42))),
% 0.35/0.55      inference('cnf', [status(esa)], [t7_tex_2])).
% 0.35/0.55  thf('4', plain,
% 0.35/0.55      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.55        | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.35/0.55        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.35/0.55           (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.35/0.55  thf(rc1_tex_2, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.35/0.55       ( ?[B:$i]:
% 0.35/0.55         ( ( v1_zfmisc_1 @ B ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.35/0.55           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ) ))).
% 0.35/0.55  thf('5', plain,
% 0.35/0.55      (![X40 : $i]: ((v1_zfmisc_1 @ (sk_B_1 @ X40)) | (v1_xboole_0 @ X40))),
% 0.35/0.55      inference('cnf', [status(esa)], [rc1_tex_2])).
% 0.35/0.55  thf(t4_subset_1, axiom,
% 0.35/0.55    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.35/0.55  thf('6', plain,
% 0.35/0.55      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.35/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.35/0.55  thf(cc5_funct_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( v1_zfmisc_1 @ A ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_zfmisc_1 @ B ) ) ) ))).
% 0.35/0.55  thf('7', plain,
% 0.35/0.55      (![X22 : $i, X23 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.35/0.55          | (v1_zfmisc_1 @ X22)
% 0.35/0.55          | ~ (v1_zfmisc_1 @ X23))),
% 0.35/0.55      inference('cnf', [status(esa)], [cc5_funct_1])).
% 0.35/0.55  thf('8', plain,
% 0.35/0.55      (![X0 : $i]: (~ (v1_zfmisc_1 @ X0) | (v1_zfmisc_1 @ k1_xboole_0))),
% 0.35/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.35/0.55  thf('9', plain,
% 0.35/0.55      (![X0 : $i]: ((v1_xboole_0 @ X0) | (v1_zfmisc_1 @ k1_xboole_0))),
% 0.35/0.55      inference('sup-', [status(thm)], ['5', '8'])).
% 0.35/0.55  thf(fc7_subset_1, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.35/0.55     ( ~( v1_xboole_0 @ ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) ) ))).
% 0.35/0.55  thf('10', plain,
% 0.35/0.55      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 0.35/0.55         X14 : $i]:
% 0.35/0.55         ~ (v1_xboole_0 @ 
% 0.35/0.55            (k6_enumset1 @ X7 @ X8 @ X9 @ X10 @ X11 @ X12 @ X13 @ X14))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc7_subset_1])).
% 0.35/0.55  thf('11', plain, ((v1_zfmisc_1 @ k1_xboole_0)),
% 0.35/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.35/0.55  thf(d3_tarski, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.35/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.35/0.55  thf('12', plain,
% 0.35/0.55      (![X4 : $i, X6 : $i]:
% 0.35/0.55         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.35/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.35/0.55  thf(d1_xboole_0, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.35/0.55  thf('13', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.35/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.35/0.55  thf('14', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.35/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.55  thf(t3_subset, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.35/0.55  thf('15', plain,
% 0.35/0.55      (![X16 : $i, X18 : $i]:
% 0.35/0.55         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 0.35/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.35/0.55  thf('16', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.35/0.55  thf('17', plain,
% 0.35/0.55      (![X22 : $i, X23 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.35/0.55          | (v1_zfmisc_1 @ X22)
% 0.35/0.55          | ~ (v1_zfmisc_1 @ X23))),
% 0.35/0.55      inference('cnf', [status(esa)], [cc5_funct_1])).
% 0.35/0.55  thf('18', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (~ (v1_xboole_0 @ X1) | ~ (v1_zfmisc_1 @ X0) | (v1_zfmisc_1 @ X1))),
% 0.35/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.55  thf('19', plain, (![X0 : $i]: ((v1_zfmisc_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.35/0.55      inference('sup-', [status(thm)], ['11', '18'])).
% 0.35/0.55  thf('20', plain,
% 0.35/0.55      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.35/0.55         (u1_struct_0 @ sk_A))
% 0.35/0.55        | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.55      inference('clc', [status(thm)], ['4', '19'])).
% 0.35/0.55  thf('21', plain,
% 0.35/0.55      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.35/0.55           (u1_struct_0 @ sk_A)))
% 0.35/0.55         <= (~
% 0.35/0.55             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.35/0.55               (u1_struct_0 @ sk_A))))),
% 0.35/0.55      inference('split', [status(esa)], ['0'])).
% 0.35/0.55  thf('22', plain,
% 0.35/0.55      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55         <= (~
% 0.35/0.55             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.35/0.55               (u1_struct_0 @ sk_A))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.35/0.55  thf(fc6_struct_0, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( ~( v7_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.35/0.55       ( ~( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.35/0.55  thf('23', plain,
% 0.35/0.55      (![X27 : $i]:
% 0.35/0.55         (~ (v1_zfmisc_1 @ (u1_struct_0 @ X27))
% 0.35/0.55          | ~ (l1_struct_0 @ X27)
% 0.35/0.55          | (v7_struct_0 @ X27))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc6_struct_0])).
% 0.35/0.55  thf('24', plain,
% 0.35/0.55      ((((v7_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.35/0.55         <= (~
% 0.35/0.55             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.35/0.55               (u1_struct_0 @ sk_A))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.35/0.55  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(dt_l1_pre_topc, axiom,
% 0.35/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.35/0.55  thf('26', plain,
% 0.35/0.55      (![X24 : $i]: ((l1_struct_0 @ X24) | ~ (l1_pre_topc @ X24))),
% 0.35/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.55  thf('27', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.35/0.55  thf('28', plain,
% 0.35/0.55      (((v7_struct_0 @ sk_A))
% 0.35/0.55         <= (~
% 0.35/0.55             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.35/0.55               (u1_struct_0 @ sk_A))))),
% 0.35/0.55      inference('demod', [status(thm)], ['24', '27'])).
% 0.35/0.55  thf('29', plain,
% 0.35/0.55      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.35/0.55         (u1_struct_0 @ sk_A))
% 0.35/0.55        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('30', plain,
% 0.35/0.55      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))
% 0.35/0.55         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.35/0.55      inference('split', [status(esa)], ['29'])).
% 0.35/0.55  thf('31', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(dt_k1_tex_2, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.35/0.55         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.35/0.55         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.35/0.55         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.35/0.55  thf('32', plain,
% 0.35/0.55      (![X36 : $i, X37 : $i]:
% 0.35/0.55         (~ (l1_pre_topc @ X36)
% 0.35/0.55          | (v2_struct_0 @ X36)
% 0.35/0.55          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X36))
% 0.35/0.55          | (m1_pre_topc @ (k1_tex_2 @ X36 @ X37) @ X36))),
% 0.35/0.55      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.35/0.55  thf('33', plain,
% 0.35/0.55      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.35/0.55        | (v2_struct_0 @ sk_A)
% 0.35/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.35/0.55  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('35', plain,
% 0.35/0.55      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.35/0.55        | (v2_struct_0 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['33', '34'])).
% 0.35/0.55  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('37', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)),
% 0.35/0.55      inference('clc', [status(thm)], ['35', '36'])).
% 0.35/0.55  thf(cc10_tex_2, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.35/0.55           ( ( ~( v2_struct_0 @ B ) ) =>
% 0.35/0.55             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tex_2 @ B @ A ) ) ) ) ) ) ))).
% 0.35/0.55  thf('38', plain,
% 0.35/0.55      (![X29 : $i, X30 : $i]:
% 0.35/0.55         (~ (m1_pre_topc @ X29 @ X30)
% 0.35/0.55          | ~ (v1_tex_2 @ X29 @ X30)
% 0.35/0.55          | (v2_struct_0 @ X29)
% 0.35/0.55          | ~ (l1_pre_topc @ X30)
% 0.35/0.55          | ~ (v7_struct_0 @ X30)
% 0.35/0.55          | (v2_struct_0 @ X30))),
% 0.35/0.55      inference('cnf', [status(esa)], [cc10_tex_2])).
% 0.35/0.55  thf('39', plain,
% 0.35/0.55      (((v2_struct_0 @ sk_A)
% 0.35/0.55        | ~ (v7_struct_0 @ sk_A)
% 0.35/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.35/0.55        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))
% 0.35/0.55        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['37', '38'])).
% 0.35/0.55  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('41', plain,
% 0.35/0.55      (((v2_struct_0 @ sk_A)
% 0.35/0.55        | ~ (v7_struct_0 @ sk_A)
% 0.35/0.55        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))
% 0.35/0.55        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['39', '40'])).
% 0.35/0.55  thf('42', plain,
% 0.35/0.55      ((((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))
% 0.35/0.55         | ~ (v7_struct_0 @ sk_A)
% 0.35/0.55         | (v2_struct_0 @ sk_A)))
% 0.35/0.55         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['30', '41'])).
% 0.35/0.55  thf('43', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('44', plain,
% 0.35/0.55      (![X36 : $i, X37 : $i]:
% 0.35/0.55         (~ (l1_pre_topc @ X36)
% 0.35/0.55          | (v2_struct_0 @ X36)
% 0.35/0.55          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X36))
% 0.35/0.55          | ~ (v2_struct_0 @ (k1_tex_2 @ X36 @ X37)))),
% 0.35/0.55      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.35/0.55  thf('45', plain,
% 0.35/0.55      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))
% 0.35/0.55        | (v2_struct_0 @ sk_A)
% 0.35/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['43', '44'])).
% 0.35/0.55  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('47', plain,
% 0.35/0.55      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) | (v2_struct_0 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['45', '46'])).
% 0.35/0.55  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('49', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))),
% 0.35/0.55      inference('clc', [status(thm)], ['47', '48'])).
% 0.35/0.55  thf('50', plain,
% 0.35/0.55      ((((v2_struct_0 @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 0.35/0.55         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.35/0.55      inference('clc', [status(thm)], ['42', '49'])).
% 0.35/0.55  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('52', plain,
% 0.35/0.55      ((~ (v7_struct_0 @ sk_A))
% 0.35/0.55         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.35/0.55      inference('clc', [status(thm)], ['50', '51'])).
% 0.35/0.55  thf('53', plain,
% 0.35/0.55      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.35/0.55         (u1_struct_0 @ sk_A))) | 
% 0.35/0.55       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['28', '52'])).
% 0.35/0.55  thf('54', plain,
% 0.35/0.55      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.35/0.55         (u1_struct_0 @ sk_A))) | 
% 0.35/0.55       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))),
% 0.35/0.55      inference('split', [status(esa)], ['29'])).
% 0.35/0.55  thf('55', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)),
% 0.35/0.55      inference('clc', [status(thm)], ['35', '36'])).
% 0.35/0.55  thf(d3_tex_2, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( l1_pre_topc @ A ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_pre_topc @ B @ A ) =>
% 0.35/0.55           ( ( v1_tex_2 @ B @ A ) <=>
% 0.35/0.55             ( ![C:$i]:
% 0.35/0.55               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.35/0.55                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.35/0.55  thf('56', plain,
% 0.35/0.55      (![X31 : $i, X32 : $i]:
% 0.35/0.55         (~ (m1_pre_topc @ X31 @ X32)
% 0.35/0.55          | ((sk_C_1 @ X31 @ X32) = (u1_struct_0 @ X31))
% 0.35/0.55          | (v1_tex_2 @ X31 @ X32)
% 0.35/0.55          | ~ (l1_pre_topc @ X32))),
% 0.35/0.55      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.35/0.55  thf('57', plain,
% 0.35/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.55        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.35/0.55        | ((sk_C_1 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.35/0.55            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['55', '56'])).
% 0.35/0.55  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('59', plain,
% 0.35/0.55      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.35/0.55        | ((sk_C_1 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.35/0.55            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))))),
% 0.35/0.55      inference('demod', [status(thm)], ['57', '58'])).
% 0.35/0.55  thf('60', plain,
% 0.35/0.55      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))
% 0.35/0.55         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.35/0.55      inference('split', [status(esa)], ['0'])).
% 0.35/0.55  thf('61', plain,
% 0.35/0.55      ((((sk_C_1 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.35/0.55          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))))
% 0.35/0.55         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['59', '60'])).
% 0.35/0.55  thf('62', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)),
% 0.35/0.55      inference('clc', [status(thm)], ['35', '36'])).
% 0.35/0.55  thf('63', plain,
% 0.35/0.55      (![X31 : $i, X32 : $i]:
% 0.35/0.55         (~ (m1_pre_topc @ X31 @ X32)
% 0.35/0.55          | (m1_subset_1 @ (sk_C_1 @ X31 @ X32) @ 
% 0.35/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.35/0.55          | (v1_tex_2 @ X31 @ X32)
% 0.35/0.55          | ~ (l1_pre_topc @ X32))),
% 0.35/0.55      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.35/0.55  thf('64', plain,
% 0.35/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.35/0.55        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.35/0.55        | (m1_subset_1 @ (sk_C_1 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A) @ 
% 0.35/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['62', '63'])).
% 0.35/0.55  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('66', plain,
% 0.35/0.55      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.35/0.55        | (m1_subset_1 @ (sk_C_1 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A) @ 
% 0.35/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.55      inference('demod', [status(thm)], ['64', '65'])).
% 0.35/0.55  thf('67', plain,
% 0.35/0.55      ((((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) @ 
% 0.35/0.55          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.55         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))
% 0.35/0.55         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.35/0.55      inference('sup+', [status(thm)], ['61', '66'])).
% 0.35/0.55  thf('68', plain,
% 0.35/0.55      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))
% 0.35/0.55         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.35/0.55      inference('split', [status(esa)], ['0'])).
% 0.35/0.55  thf('69', plain,
% 0.35/0.55      (((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) @ 
% 0.35/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.35/0.55         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.35/0.55      inference('clc', [status(thm)], ['67', '68'])).
% 0.35/0.55  thf(d7_subset_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.55       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.35/0.55  thf('70', plain,
% 0.35/0.55      (![X34 : $i, X35 : $i]:
% 0.35/0.55         (((X35) = (X34))
% 0.35/0.55          | (v1_subset_1 @ X35 @ X34)
% 0.35/0.55          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 0.35/0.55      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.35/0.55  thf('71', plain,
% 0.35/0.55      ((((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) @ 
% 0.35/0.55          (u1_struct_0 @ sk_A))
% 0.35/0.55         | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) = (u1_struct_0 @ sk_A))))
% 0.35/0.55         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['69', '70'])).
% 0.35/0.55  thf('72', plain,
% 0.35/0.55      ((((sk_C_1 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.35/0.55          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))))
% 0.35/0.55         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['59', '60'])).
% 0.35/0.55  thf('73', plain,
% 0.35/0.55      (![X31 : $i, X32 : $i]:
% 0.35/0.55         (~ (m1_pre_topc @ X31 @ X32)
% 0.35/0.55          | ~ (v1_subset_1 @ (sk_C_1 @ X31 @ X32) @ (u1_struct_0 @ X32))
% 0.35/0.55          | (v1_tex_2 @ X31 @ X32)
% 0.35/0.55          | ~ (l1_pre_topc @ X32))),
% 0.35/0.55      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.35/0.55  thf('74', plain,
% 0.35/0.55      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) @ 
% 0.35/0.55            (u1_struct_0 @ sk_A))
% 0.35/0.55         | ~ (l1_pre_topc @ sk_A)
% 0.35/0.55         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.35/0.55         | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))
% 0.35/0.55         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['72', '73'])).
% 0.35/0.55  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('76', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)),
% 0.35/0.55      inference('clc', [status(thm)], ['35', '36'])).
% 0.35/0.55  thf('77', plain,
% 0.35/0.55      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) @ 
% 0.35/0.55            (u1_struct_0 @ sk_A))
% 0.35/0.55         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))
% 0.35/0.55         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.35/0.55      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.35/0.55  thf('78', plain,
% 0.35/0.55      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))
% 0.35/0.55         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.35/0.55      inference('split', [status(esa)], ['0'])).
% 0.35/0.55  thf('79', plain,
% 0.35/0.55      ((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) @ 
% 0.35/0.55           (u1_struct_0 @ sk_A)))
% 0.35/0.55         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.35/0.55      inference('clc', [status(thm)], ['77', '78'])).
% 0.35/0.55  thf('80', plain,
% 0.35/0.55      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) = (u1_struct_0 @ sk_A)))
% 0.35/0.55         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.35/0.55      inference('clc', [status(thm)], ['71', '79'])).
% 0.35/0.55  thf(fc7_struct_0, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.35/0.55       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.35/0.55  thf('81', plain,
% 0.35/0.55      (![X28 : $i]:
% 0.35/0.55         ((v1_zfmisc_1 @ (u1_struct_0 @ X28))
% 0.35/0.55          | ~ (l1_struct_0 @ X28)
% 0.35/0.55          | ~ (v7_struct_0 @ X28))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.35/0.55  thf('82', plain,
% 0.35/0.55      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.35/0.55         | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))
% 0.35/0.55         | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))))
% 0.35/0.55         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.35/0.55      inference('sup+', [status(thm)], ['80', '81'])).
% 0.35/0.55  thf('83', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(fc2_tex_2, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.35/0.55         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.55       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.35/0.55         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.35/0.55         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.35/0.55  thf('84', plain,
% 0.35/0.55      (![X38 : $i, X39 : $i]:
% 0.35/0.55         (~ (l1_pre_topc @ X38)
% 0.35/0.55          | (v2_struct_0 @ X38)
% 0.35/0.55          | ~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X38))
% 0.35/0.55          | (v7_struct_0 @ (k1_tex_2 @ X38 @ X39)))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.35/0.55  thf('85', plain,
% 0.35/0.55      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))
% 0.35/0.55        | (v2_struct_0 @ sk_A)
% 0.35/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['83', '84'])).
% 0.35/0.55  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('87', plain,
% 0.35/0.55      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) | (v2_struct_0 @ sk_A))),
% 0.35/0.55      inference('demod', [status(thm)], ['85', '86'])).
% 0.35/0.55  thf('88', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('89', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))),
% 0.35/0.55      inference('clc', [status(thm)], ['87', '88'])).
% 0.35/0.55  thf('90', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)),
% 0.35/0.55      inference('clc', [status(thm)], ['35', '36'])).
% 0.35/0.55  thf(dt_m1_pre_topc, axiom,
% 0.35/0.56    (![A:$i]:
% 0.35/0.56     ( ( l1_pre_topc @ A ) =>
% 0.35/0.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.35/0.56  thf('91', plain,
% 0.35/0.56      (![X25 : $i, X26 : $i]:
% 0.35/0.56         (~ (m1_pre_topc @ X25 @ X26)
% 0.35/0.56          | (l1_pre_topc @ X25)
% 0.35/0.56          | ~ (l1_pre_topc @ X26))),
% 0.35/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.35/0.56  thf('92', plain,
% 0.35/0.56      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2)))),
% 0.35/0.56      inference('sup-', [status(thm)], ['90', '91'])).
% 0.35/0.56  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('94', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2))),
% 0.35/0.56      inference('demod', [status(thm)], ['92', '93'])).
% 0.35/0.56  thf('95', plain,
% 0.35/0.56      (![X24 : $i]: ((l1_struct_0 @ X24) | ~ (l1_pre_topc @ X24))),
% 0.35/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.56  thf('96', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))),
% 0.35/0.56      inference('sup-', [status(thm)], ['94', '95'])).
% 0.35/0.56  thf('97', plain,
% 0.35/0.56      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.35/0.56      inference('demod', [status(thm)], ['82', '89', '96'])).
% 0.35/0.56  thf('98', plain,
% 0.35/0.56      (![X27 : $i]:
% 0.35/0.56         (~ (v1_zfmisc_1 @ (u1_struct_0 @ X27))
% 0.35/0.56          | ~ (l1_struct_0 @ X27)
% 0.35/0.56          | (v7_struct_0 @ X27))),
% 0.35/0.56      inference('cnf', [status(esa)], [fc6_struct_0])).
% 0.35/0.56  thf('99', plain,
% 0.35/0.56      ((((v7_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.35/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.35/0.56      inference('sup-', [status(thm)], ['97', '98'])).
% 0.35/0.56  thf('100', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.35/0.56  thf('101', plain,
% 0.35/0.56      (((v7_struct_0 @ sk_A))
% 0.35/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.35/0.56      inference('demod', [status(thm)], ['99', '100'])).
% 0.35/0.56  thf('102', plain,
% 0.35/0.56      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.35/0.56         (u1_struct_0 @ sk_A)))
% 0.35/0.56         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.35/0.56               (u1_struct_0 @ sk_A))))),
% 0.35/0.56      inference('split', [status(esa)], ['29'])).
% 0.35/0.56  thf(t8_tex_2, axiom,
% 0.35/0.56    (![A:$i]:
% 0.35/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.35/0.56       ( ![B:$i]:
% 0.35/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.56           ( ~( ( v1_subset_1 @
% 0.35/0.56                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.35/0.56                  ( u1_struct_0 @ A ) ) & 
% 0.35/0.56                ( v7_struct_0 @ A ) ) ) ) ) ))).
% 0.35/0.56  thf('103', plain,
% 0.35/0.56      (![X43 : $i, X44 : $i]:
% 0.35/0.56         (~ (m1_subset_1 @ X43 @ (u1_struct_0 @ X44))
% 0.35/0.56          | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X44) @ X43) @ 
% 0.35/0.56               (u1_struct_0 @ X44))
% 0.35/0.56          | ~ (v7_struct_0 @ X44)
% 0.35/0.56          | ~ (l1_struct_0 @ X44)
% 0.35/0.56          | (v2_struct_0 @ X44))),
% 0.35/0.56      inference('cnf', [status(esa)], [t8_tex_2])).
% 0.35/0.56  thf('104', plain,
% 0.35/0.56      ((((v2_struct_0 @ sk_A)
% 0.35/0.56         | ~ (l1_struct_0 @ sk_A)
% 0.35/0.56         | ~ (v7_struct_0 @ sk_A)
% 0.35/0.56         | ~ (m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))
% 0.35/0.56         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.35/0.56               (u1_struct_0 @ sk_A))))),
% 0.35/0.56      inference('sup-', [status(thm)], ['102', '103'])).
% 0.35/0.56  thf('105', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.35/0.56  thf('106', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('107', plain,
% 0.35/0.56      ((((v2_struct_0 @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 0.35/0.56         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.35/0.56               (u1_struct_0 @ sk_A))))),
% 0.35/0.56      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.35/0.56  thf('108', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.56  thf('109', plain,
% 0.35/0.56      ((~ (v7_struct_0 @ sk_A))
% 0.35/0.56         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.35/0.56               (u1_struct_0 @ sk_A))))),
% 0.35/0.56      inference('clc', [status(thm)], ['107', '108'])).
% 0.35/0.56  thf('110', plain,
% 0.35/0.56      (~
% 0.35/0.56       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.35/0.56         (u1_struct_0 @ sk_A))) | 
% 0.35/0.56       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))),
% 0.35/0.56      inference('sup-', [status(thm)], ['101', '109'])).
% 0.35/0.56  thf('111', plain, ($false),
% 0.35/0.56      inference('sat_resolution*', [status(thm)], ['1', '53', '54', '110'])).
% 0.35/0.56  
% 0.35/0.56  % SZS output end Refutation
% 0.35/0.56  
% 0.35/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
