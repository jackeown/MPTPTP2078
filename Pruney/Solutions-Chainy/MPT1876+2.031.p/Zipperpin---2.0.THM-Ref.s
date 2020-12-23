%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.27CckPnuHa

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:00 EST 2020

% Result     : Theorem 1.02s
% Output     : Refutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 562 expanded)
%              Number of leaves         :   40 ( 167 expanded)
%              Depth                    :   34
%              Number of atoms          : 1378 (6537 expanded)
%              Number of equality atoms :   25 (  67 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t44_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ( v1_zfmisc_1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v2_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( ( v2_tex_2 @ B @ A )
            <=> ( v1_zfmisc_1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_tex_2])).

thf('0',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
   <= ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X26: $i] :
      ( ~ ( v1_zfmisc_1 @ X26 )
      | ( X26
        = ( k6_domain_1 @ X26 @ ( sk_B @ X26 ) ) )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('4',plain,(
    ! [X26: $i] :
      ( ~ ( v1_zfmisc_1 @ X26 )
      | ( m1_subset_1 @ ( sk_B @ X26 ) @ X26 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( ( k6_domain_1 @ X20 @ X21 )
        = ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    ! [X26: $i] :
      ( ~ ( v1_zfmisc_1 @ X26 )
      | ( m1_subset_1 @ ( sk_B @ X26 ) @ X26 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ X11 )
      | ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','23'])).

thf('25',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( m1_subset_1 @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('26',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( ( k6_domain_1 @ X20 @ X21 )
        = ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('28',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
        = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
        = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('31',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X38 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X38 ) @ X37 ) @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('32',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['29','37'])).

thf('39',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_zfmisc_1 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['9','39'])).

thf('41',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('42',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['42','43'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t35_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v1_xboole_0 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( v2_tex_2 @ X35 @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t35_tex_2])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
      | ( v2_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['54','55'])).

thf(t27_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( B
              = ( u1_struct_0 @ A ) )
           => ( ( v2_tex_2 @ B @ A )
            <=> ( v1_tdlat_3 @ A ) ) ) ) ) )).

thf('57',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v2_tex_2 @ X33 @ X34 )
      | ( v1_tdlat_3 @ X34 )
      | ( X33
       != ( u1_struct_0 @ X34 ) )
      | ~ ( l1_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t27_tex_2])).

thf('58',plain,(
    ! [X34: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ( v1_tdlat_3 @ X34 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X34 ) @ X34 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X34 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('60',plain,(
    ! [X34: $i] :
      ( ( v2_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ( v1_tdlat_3 @ X34 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X34 ) @ X34 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ( v1_tdlat_3 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t43_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf('65',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( v2_tex_2 @ X39 @ X40 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v1_tdlat_3 @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t43_tex_2])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_tex_2 @ sk_B_1 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['63','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('76',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','76'])).

thf('78',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['1','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ? [C: $i] :
              ( ( B
                = ( u1_struct_0 @ C ) )
              & ( m1_pre_topc @ C @ A )
              & ( v1_pre_topc @ C )
              & ~ ( v2_struct_0 @ C ) ) ) ) )).

thf('80',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( X28
        = ( u1_struct_0 @ ( sk_C_1 @ X28 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('88',plain,(
    ! [X19: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ~ ( v7_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('89',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( m1_pre_topc @ ( sk_C_1 @ X28 @ X29 ) @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['96','97'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('99',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( l1_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('100',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['100','101'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('103',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('104',plain,(
    l1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','104'])).

thf('106',plain,(
    m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['96','97'])).

thf(cc32_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( ~ ( v2_struct_0 @ B )
              & ~ ( v7_struct_0 @ B ) )
           => ( ~ ( v2_struct_0 @ B )
              & ~ ( v1_tdlat_3 @ B ) ) ) ) ) )).

thf('107',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( v1_tdlat_3 @ X24 )
      | ( v7_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_tdlat_3 @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc32_tex_2])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','109','110','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf(t26_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( v2_tex_2 @ C @ A )
                <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) )).

thf('115',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( m1_pre_topc @ X30 @ X31 )
      | ( X32
       != ( u1_struct_0 @ X30 ) )
      | ~ ( v2_tex_2 @ X32 @ X31 )
      | ( v1_tdlat_3 @ X30 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('116',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X30 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( v1_tdlat_3 @ X30 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X30 ) @ X31 )
      | ~ ( m1_pre_topc @ X30 @ X31 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) @ X0 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','116'])).

thf('118',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ X0 )
      | ~ ( v2_tex_2 @ sk_B_1 @ X0 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','119'])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('123',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('124',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','76','123'])).

thf('125',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['122','124'])).

thf('126',plain,(
    m1_pre_topc @ ( sk_C_1 @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['96','97'])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['120','121','125','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ X28 @ X29 ) )
      | ~ ( l1_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('132',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,(
    v1_tdlat_3 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['129','138'])).

thf('140',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['112','139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('144',plain,(
    v7_struct_0 @ ( sk_C_1 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,(
    v1_zfmisc_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['105','144'])).

thf('146',plain,(
    $false ),
    inference(demod,[status(thm)],['78','145'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.27CckPnuHa
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:37:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.02/1.21  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.02/1.21  % Solved by: fo/fo7.sh
% 1.02/1.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.02/1.21  % done 536 iterations in 0.744s
% 1.02/1.21  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.02/1.21  % SZS output start Refutation
% 1.02/1.21  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.02/1.21  thf(sk_A_type, type, sk_A: $i).
% 1.02/1.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.02/1.21  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.02/1.21  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.02/1.21  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 1.02/1.21  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.02/1.21  thf(sk_B_type, type, sk_B: $i > $i).
% 1.02/1.21  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 1.02/1.21  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.02/1.21  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.02/1.21  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.02/1.21  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.02/1.21  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.02/1.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.02/1.21  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.02/1.21  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 1.02/1.21  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 1.02/1.21  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.02/1.21  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.02/1.21  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 1.02/1.21  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 1.02/1.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.02/1.21  thf(t44_tex_2, conjecture,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 1.02/1.21         ( l1_pre_topc @ A ) ) =>
% 1.02/1.21       ( ![B:$i]:
% 1.02/1.21         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.02/1.21             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.02/1.21           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 1.02/1.21  thf(zf_stmt_0, negated_conjecture,
% 1.02/1.21    (~( ![A:$i]:
% 1.02/1.21        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.02/1.21            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.02/1.21          ( ![B:$i]:
% 1.02/1.21            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.02/1.21                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.02/1.21              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 1.02/1.21    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 1.02/1.21  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('1', plain, ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 1.02/1.21      inference('split', [status(esa)], ['0'])).
% 1.02/1.21  thf('2', plain,
% 1.02/1.21      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.02/1.21      inference('split', [status(esa)], ['0'])).
% 1.02/1.21  thf(d1_tex_2, axiom,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.02/1.21       ( ( v1_zfmisc_1 @ A ) <=>
% 1.02/1.21         ( ?[B:$i]:
% 1.02/1.21           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 1.02/1.21  thf('3', plain,
% 1.02/1.21      (![X26 : $i]:
% 1.02/1.21         (~ (v1_zfmisc_1 @ X26)
% 1.02/1.21          | ((X26) = (k6_domain_1 @ X26 @ (sk_B @ X26)))
% 1.02/1.21          | (v1_xboole_0 @ X26))),
% 1.02/1.21      inference('cnf', [status(esa)], [d1_tex_2])).
% 1.02/1.21  thf('4', plain,
% 1.02/1.21      (![X26 : $i]:
% 1.02/1.21         (~ (v1_zfmisc_1 @ X26)
% 1.02/1.21          | (m1_subset_1 @ (sk_B @ X26) @ X26)
% 1.02/1.21          | (v1_xboole_0 @ X26))),
% 1.02/1.21      inference('cnf', [status(esa)], [d1_tex_2])).
% 1.02/1.21  thf(redefinition_k6_domain_1, axiom,
% 1.02/1.21    (![A:$i,B:$i]:
% 1.02/1.21     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.02/1.21       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 1.02/1.21  thf('5', plain,
% 1.02/1.21      (![X20 : $i, X21 : $i]:
% 1.02/1.21         ((v1_xboole_0 @ X20)
% 1.02/1.21          | ~ (m1_subset_1 @ X21 @ X20)
% 1.02/1.21          | ((k6_domain_1 @ X20 @ X21) = (k1_tarski @ X21)))),
% 1.02/1.21      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.02/1.21  thf('6', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v1_xboole_0 @ X0)
% 1.02/1.21          | ~ (v1_zfmisc_1 @ X0)
% 1.02/1.21          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 1.02/1.21          | (v1_xboole_0 @ X0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['4', '5'])).
% 1.02/1.21  thf('7', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 1.02/1.21          | ~ (v1_zfmisc_1 @ X0)
% 1.02/1.21          | (v1_xboole_0 @ X0))),
% 1.02/1.21      inference('simplify', [status(thm)], ['6'])).
% 1.02/1.21  thf('8', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (((X0) = (k1_tarski @ (sk_B @ X0)))
% 1.02/1.21          | (v1_xboole_0 @ X0)
% 1.02/1.21          | ~ (v1_zfmisc_1 @ X0)
% 1.02/1.21          | (v1_xboole_0 @ X0)
% 1.02/1.21          | ~ (v1_zfmisc_1 @ X0))),
% 1.02/1.21      inference('sup+', [status(thm)], ['3', '7'])).
% 1.02/1.21  thf('9', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (v1_zfmisc_1 @ X0)
% 1.02/1.21          | (v1_xboole_0 @ X0)
% 1.02/1.21          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 1.02/1.21      inference('simplify', [status(thm)], ['8'])).
% 1.02/1.21  thf('10', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('11', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.02/1.21      inference('split', [status(esa)], ['10'])).
% 1.02/1.21  thf('12', plain,
% 1.02/1.21      (![X26 : $i]:
% 1.02/1.21         (~ (v1_zfmisc_1 @ X26)
% 1.02/1.21          | (m1_subset_1 @ (sk_B @ X26) @ X26)
% 1.02/1.21          | (v1_xboole_0 @ X26))),
% 1.02/1.21      inference('cnf', [status(esa)], [d1_tex_2])).
% 1.02/1.21  thf(d2_subset_1, axiom,
% 1.02/1.21    (![A:$i,B:$i]:
% 1.02/1.21     ( ( ( v1_xboole_0 @ A ) =>
% 1.02/1.21         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.02/1.21       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.02/1.21         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.02/1.21  thf('13', plain,
% 1.02/1.21      (![X10 : $i, X11 : $i]:
% 1.02/1.21         (~ (m1_subset_1 @ X10 @ X11)
% 1.02/1.21          | (r2_hidden @ X10 @ X11)
% 1.02/1.21          | (v1_xboole_0 @ X11))),
% 1.02/1.21      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.02/1.21  thf('14', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v1_xboole_0 @ X0)
% 1.02/1.21          | ~ (v1_zfmisc_1 @ X0)
% 1.02/1.21          | (v1_xboole_0 @ X0)
% 1.02/1.21          | (r2_hidden @ (sk_B @ X0) @ X0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['12', '13'])).
% 1.02/1.21  thf('15', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((r2_hidden @ (sk_B @ X0) @ X0)
% 1.02/1.21          | ~ (v1_zfmisc_1 @ X0)
% 1.02/1.21          | (v1_xboole_0 @ X0))),
% 1.02/1.21      inference('simplify', [status(thm)], ['14'])).
% 1.02/1.21  thf('16', plain,
% 1.02/1.21      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf(t3_subset, axiom,
% 1.02/1.21    (![A:$i,B:$i]:
% 1.02/1.21     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.02/1.21  thf('17', plain,
% 1.02/1.21      (![X13 : $i, X14 : $i]:
% 1.02/1.21         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 1.02/1.21      inference('cnf', [status(esa)], [t3_subset])).
% 1.02/1.21  thf('18', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 1.02/1.21      inference('sup-', [status(thm)], ['16', '17'])).
% 1.02/1.21  thf(d3_tarski, axiom,
% 1.02/1.21    (![A:$i,B:$i]:
% 1.02/1.21     ( ( r1_tarski @ A @ B ) <=>
% 1.02/1.21       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.02/1.21  thf('19', plain,
% 1.02/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.21         (~ (r2_hidden @ X0 @ X1)
% 1.02/1.21          | (r2_hidden @ X0 @ X2)
% 1.02/1.21          | ~ (r1_tarski @ X1 @ X2))),
% 1.02/1.21      inference('cnf', [status(esa)], [d3_tarski])).
% 1.02/1.21  thf('20', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.02/1.21      inference('sup-', [status(thm)], ['18', '19'])).
% 1.02/1.21  thf('21', plain,
% 1.02/1.21      (((v1_xboole_0 @ sk_B_1)
% 1.02/1.21        | ~ (v1_zfmisc_1 @ sk_B_1)
% 1.02/1.21        | (r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['15', '20'])).
% 1.02/1.21  thf('22', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('23', plain,
% 1.02/1.21      (((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 1.02/1.21        | ~ (v1_zfmisc_1 @ sk_B_1))),
% 1.02/1.21      inference('clc', [status(thm)], ['21', '22'])).
% 1.02/1.21  thf('24', plain,
% 1.02/1.21      (((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))
% 1.02/1.21         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['11', '23'])).
% 1.02/1.21  thf('25', plain,
% 1.02/1.21      (![X10 : $i, X11 : $i]:
% 1.02/1.21         (~ (r2_hidden @ X10 @ X11)
% 1.02/1.21          | (m1_subset_1 @ X10 @ X11)
% 1.02/1.21          | (v1_xboole_0 @ X11))),
% 1.02/1.21      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.02/1.21  thf('26', plain,
% 1.02/1.21      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.02/1.21         | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 1.02/1.21         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['24', '25'])).
% 1.02/1.21  thf('27', plain,
% 1.02/1.21      (![X20 : $i, X21 : $i]:
% 1.02/1.21         ((v1_xboole_0 @ X20)
% 1.02/1.21          | ~ (m1_subset_1 @ X21 @ X20)
% 1.02/1.21          | ((k6_domain_1 @ X20 @ X21) = (k1_tarski @ X21)))),
% 1.02/1.21      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.02/1.21  thf('28', plain,
% 1.02/1.21      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.02/1.21         | ((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 1.02/1.21             = (k1_tarski @ (sk_B @ sk_B_1)))
% 1.02/1.21         | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['26', '27'])).
% 1.02/1.21  thf('29', plain,
% 1.02/1.21      (((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 1.02/1.21           = (k1_tarski @ (sk_B @ sk_B_1)))
% 1.02/1.21         | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.02/1.21      inference('simplify', [status(thm)], ['28'])).
% 1.02/1.21  thf('30', plain,
% 1.02/1.21      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.02/1.21         | (m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 1.02/1.21         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['24', '25'])).
% 1.02/1.21  thf(t36_tex_2, axiom,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.02/1.21       ( ![B:$i]:
% 1.02/1.21         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.02/1.21           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 1.02/1.21  thf('31', plain,
% 1.02/1.21      (![X37 : $i, X38 : $i]:
% 1.02/1.21         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X38))
% 1.02/1.21          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X38) @ X37) @ X38)
% 1.02/1.21          | ~ (l1_pre_topc @ X38)
% 1.02/1.21          | ~ (v2_pre_topc @ X38)
% 1.02/1.21          | (v2_struct_0 @ X38))),
% 1.02/1.21      inference('cnf', [status(esa)], [t36_tex_2])).
% 1.02/1.21  thf('32', plain,
% 1.02/1.21      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.02/1.21         | (v2_struct_0 @ sk_A)
% 1.02/1.21         | ~ (v2_pre_topc @ sk_A)
% 1.02/1.21         | ~ (l1_pre_topc @ sk_A)
% 1.02/1.21         | (v2_tex_2 @ 
% 1.02/1.21            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ sk_A)))
% 1.02/1.21         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['30', '31'])).
% 1.02/1.21  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('35', plain,
% 1.02/1.21      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.02/1.21         | (v2_struct_0 @ sk_A)
% 1.02/1.21         | (v2_tex_2 @ 
% 1.02/1.21            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ sk_A)))
% 1.02/1.21         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.02/1.21      inference('demod', [status(thm)], ['32', '33', '34'])).
% 1.02/1.21  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('37', plain,
% 1.02/1.21      ((((v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 1.02/1.21          sk_A)
% 1.02/1.21         | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.02/1.21      inference('clc', [status(thm)], ['35', '36'])).
% 1.02/1.21  thf('38', plain,
% 1.02/1.21      ((((v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)
% 1.02/1.21         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.02/1.21         | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.02/1.21      inference('sup+', [status(thm)], ['29', '37'])).
% 1.02/1.21  thf('39', plain,
% 1.02/1.21      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.02/1.21         | (v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)))
% 1.02/1.21         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.02/1.21      inference('simplify', [status(thm)], ['38'])).
% 1.02/1.21  thf('40', plain,
% 1.02/1.21      ((((v2_tex_2 @ sk_B_1 @ sk_A)
% 1.02/1.21         | (v1_xboole_0 @ sk_B_1)
% 1.02/1.21         | ~ (v1_zfmisc_1 @ sk_B_1)
% 1.02/1.21         | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.02/1.21      inference('sup+', [status(thm)], ['9', '39'])).
% 1.02/1.21  thf('41', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.02/1.21      inference('split', [status(esa)], ['10'])).
% 1.02/1.21  thf('42', plain,
% 1.02/1.21      ((((v2_tex_2 @ sk_B_1 @ sk_A)
% 1.02/1.21         | (v1_xboole_0 @ sk_B_1)
% 1.02/1.21         | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.02/1.21      inference('demod', [status(thm)], ['40', '41'])).
% 1.02/1.21  thf('43', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('44', plain,
% 1.02/1.21      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v2_tex_2 @ sk_B_1 @ sk_A)))
% 1.02/1.21         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.02/1.21      inference('clc', [status(thm)], ['42', '43'])).
% 1.02/1.21  thf(d10_xboole_0, axiom,
% 1.02/1.21    (![A:$i,B:$i]:
% 1.02/1.21     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.02/1.21  thf('45', plain,
% 1.02/1.21      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 1.02/1.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.02/1.21  thf('46', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.02/1.21      inference('simplify', [status(thm)], ['45'])).
% 1.02/1.21  thf('47', plain,
% 1.02/1.21      (![X13 : $i, X15 : $i]:
% 1.02/1.21         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 1.02/1.21      inference('cnf', [status(esa)], [t3_subset])).
% 1.02/1.21  thf('48', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['46', '47'])).
% 1.02/1.21  thf(t35_tex_2, axiom,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.02/1.21       ( ![B:$i]:
% 1.02/1.21         ( ( ( v1_xboole_0 @ B ) & 
% 1.02/1.21             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.02/1.21           ( v2_tex_2 @ B @ A ) ) ) ))).
% 1.02/1.21  thf('49', plain,
% 1.02/1.21      (![X35 : $i, X36 : $i]:
% 1.02/1.21         (~ (v1_xboole_0 @ X35)
% 1.02/1.21          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 1.02/1.21          | (v2_tex_2 @ X35 @ X36)
% 1.02/1.21          | ~ (l1_pre_topc @ X36)
% 1.02/1.21          | ~ (v2_pre_topc @ X36)
% 1.02/1.21          | (v2_struct_0 @ X36))),
% 1.02/1.21      inference('cnf', [status(esa)], [t35_tex_2])).
% 1.02/1.21  thf('50', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         ((v2_struct_0 @ X0)
% 1.02/1.21          | ~ (v2_pre_topc @ X0)
% 1.02/1.21          | ~ (l1_pre_topc @ X0)
% 1.02/1.21          | (v2_tex_2 @ (u1_struct_0 @ X0) @ X0)
% 1.02/1.21          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['48', '49'])).
% 1.02/1.21  thf('51', plain,
% 1.02/1.21      ((((v2_tex_2 @ sk_B_1 @ sk_A)
% 1.02/1.21         | (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 1.02/1.21         | ~ (l1_pre_topc @ sk_A)
% 1.02/1.21         | ~ (v2_pre_topc @ sk_A)
% 1.02/1.21         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['44', '50'])).
% 1.02/1.21  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('54', plain,
% 1.02/1.21      ((((v2_tex_2 @ sk_B_1 @ sk_A)
% 1.02/1.21         | (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 1.02/1.21         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.02/1.21      inference('demod', [status(thm)], ['51', '52', '53'])).
% 1.02/1.21  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('56', plain,
% 1.02/1.21      ((((v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A)))
% 1.02/1.21         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.02/1.21      inference('clc', [status(thm)], ['54', '55'])).
% 1.02/1.21  thf(t27_tex_2, axiom,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.02/1.21       ( ![B:$i]:
% 1.02/1.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.21           ( ( ( B ) = ( u1_struct_0 @ A ) ) =>
% 1.02/1.21             ( ( v2_tex_2 @ B @ A ) <=> ( v1_tdlat_3 @ A ) ) ) ) ) ))).
% 1.02/1.21  thf('57', plain,
% 1.02/1.21      (![X33 : $i, X34 : $i]:
% 1.02/1.21         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 1.02/1.21          | ~ (v2_tex_2 @ X33 @ X34)
% 1.02/1.21          | (v1_tdlat_3 @ X34)
% 1.02/1.21          | ((X33) != (u1_struct_0 @ X34))
% 1.02/1.21          | ~ (l1_pre_topc @ X34)
% 1.02/1.21          | (v2_struct_0 @ X34))),
% 1.02/1.21      inference('cnf', [status(esa)], [t27_tex_2])).
% 1.02/1.21  thf('58', plain,
% 1.02/1.21      (![X34 : $i]:
% 1.02/1.21         ((v2_struct_0 @ X34)
% 1.02/1.21          | ~ (l1_pre_topc @ X34)
% 1.02/1.21          | (v1_tdlat_3 @ X34)
% 1.02/1.21          | ~ (v2_tex_2 @ (u1_struct_0 @ X34) @ X34)
% 1.02/1.21          | ~ (m1_subset_1 @ (u1_struct_0 @ X34) @ 
% 1.02/1.21               (k1_zfmisc_1 @ (u1_struct_0 @ X34))))),
% 1.02/1.21      inference('simplify', [status(thm)], ['57'])).
% 1.02/1.21  thf('59', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['46', '47'])).
% 1.02/1.21  thf('60', plain,
% 1.02/1.21      (![X34 : $i]:
% 1.02/1.21         ((v2_struct_0 @ X34)
% 1.02/1.21          | ~ (l1_pre_topc @ X34)
% 1.02/1.21          | (v1_tdlat_3 @ X34)
% 1.02/1.21          | ~ (v2_tex_2 @ (u1_struct_0 @ X34) @ X34))),
% 1.02/1.21      inference('demod', [status(thm)], ['58', '59'])).
% 1.02/1.21  thf('61', plain,
% 1.02/1.21      ((((v2_tex_2 @ sk_B_1 @ sk_A)
% 1.02/1.21         | (v1_tdlat_3 @ sk_A)
% 1.02/1.21         | ~ (l1_pre_topc @ sk_A)
% 1.02/1.21         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['56', '60'])).
% 1.02/1.21  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('63', plain,
% 1.02/1.21      ((((v2_tex_2 @ sk_B_1 @ sk_A)
% 1.02/1.21         | (v1_tdlat_3 @ sk_A)
% 1.02/1.21         | (v2_struct_0 @ sk_A))) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.02/1.21      inference('demod', [status(thm)], ['61', '62'])).
% 1.02/1.21  thf('64', plain,
% 1.02/1.21      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf(t43_tex_2, axiom,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 1.02/1.21         ( l1_pre_topc @ A ) ) =>
% 1.02/1.21       ( ![B:$i]:
% 1.02/1.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.21           ( v2_tex_2 @ B @ A ) ) ) ))).
% 1.02/1.21  thf('65', plain,
% 1.02/1.21      (![X39 : $i, X40 : $i]:
% 1.02/1.21         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 1.02/1.21          | (v2_tex_2 @ X39 @ X40)
% 1.02/1.21          | ~ (l1_pre_topc @ X40)
% 1.02/1.21          | ~ (v1_tdlat_3 @ X40)
% 1.02/1.21          | ~ (v2_pre_topc @ X40)
% 1.02/1.21          | (v2_struct_0 @ X40))),
% 1.02/1.21      inference('cnf', [status(esa)], [t43_tex_2])).
% 1.02/1.21  thf('66', plain,
% 1.02/1.21      (((v2_struct_0 @ sk_A)
% 1.02/1.21        | ~ (v2_pre_topc @ sk_A)
% 1.02/1.21        | ~ (v1_tdlat_3 @ sk_A)
% 1.02/1.21        | ~ (l1_pre_topc @ sk_A)
% 1.02/1.21        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.02/1.21      inference('sup-', [status(thm)], ['64', '65'])).
% 1.02/1.21  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('69', plain,
% 1.02/1.21      (((v2_struct_0 @ sk_A)
% 1.02/1.21        | ~ (v1_tdlat_3 @ sk_A)
% 1.02/1.21        | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.02/1.21      inference('demod', [status(thm)], ['66', '67', '68'])).
% 1.02/1.21  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('71', plain, (((v2_tex_2 @ sk_B_1 @ sk_A) | ~ (v1_tdlat_3 @ sk_A))),
% 1.02/1.21      inference('clc', [status(thm)], ['69', '70'])).
% 1.02/1.21  thf('72', plain,
% 1.02/1.21      ((((v2_struct_0 @ sk_A) | (v2_tex_2 @ sk_B_1 @ sk_A)))
% 1.02/1.21         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.02/1.21      inference('clc', [status(thm)], ['63', '71'])).
% 1.02/1.21  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('74', plain,
% 1.02/1.21      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.02/1.21      inference('clc', [status(thm)], ['72', '73'])).
% 1.02/1.21  thf('75', plain,
% 1.02/1.21      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.02/1.21      inference('split', [status(esa)], ['0'])).
% 1.02/1.21  thf('76', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ~ ((v1_zfmisc_1 @ sk_B_1))),
% 1.02/1.21      inference('sup-', [status(thm)], ['74', '75'])).
% 1.02/1.21  thf('77', plain, (~ ((v1_zfmisc_1 @ sk_B_1))),
% 1.02/1.21      inference('sat_resolution*', [status(thm)], ['2', '76'])).
% 1.02/1.21  thf('78', plain, (~ (v1_zfmisc_1 @ sk_B_1)),
% 1.02/1.21      inference('simpl_trail', [status(thm)], ['1', '77'])).
% 1.02/1.21  thf('79', plain,
% 1.02/1.21      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf(t10_tsep_1, axiom,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.02/1.21       ( ![B:$i]:
% 1.02/1.21         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.02/1.21             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.02/1.21           ( ?[C:$i]:
% 1.02/1.21             ( ( ( B ) = ( u1_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) & 
% 1.02/1.21               ( v1_pre_topc @ C ) & ( ~( v2_struct_0 @ C ) ) ) ) ) ) ))).
% 1.02/1.21  thf('80', plain,
% 1.02/1.21      (![X28 : $i, X29 : $i]:
% 1.02/1.21         ((v1_xboole_0 @ X28)
% 1.02/1.21          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 1.02/1.21          | ((X28) = (u1_struct_0 @ (sk_C_1 @ X28 @ X29)))
% 1.02/1.21          | ~ (l1_pre_topc @ X29)
% 1.02/1.21          | (v2_struct_0 @ X29))),
% 1.02/1.21      inference('cnf', [status(esa)], [t10_tsep_1])).
% 1.02/1.21  thf('81', plain,
% 1.02/1.21      (((v2_struct_0 @ sk_A)
% 1.02/1.21        | ~ (l1_pre_topc @ sk_A)
% 1.02/1.21        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 1.02/1.21        | (v1_xboole_0 @ sk_B_1))),
% 1.02/1.21      inference('sup-', [status(thm)], ['79', '80'])).
% 1.02/1.21  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('83', plain,
% 1.02/1.21      (((v2_struct_0 @ sk_A)
% 1.02/1.21        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))
% 1.02/1.21        | (v1_xboole_0 @ sk_B_1))),
% 1.02/1.21      inference('demod', [status(thm)], ['81', '82'])).
% 1.02/1.21  thf('84', plain, (~ (v2_struct_0 @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('85', plain,
% 1.02/1.21      (((v1_xboole_0 @ sk_B_1)
% 1.02/1.21        | ((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))))),
% 1.02/1.21      inference('clc', [status(thm)], ['83', '84'])).
% 1.02/1.21  thf('86', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('87', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 1.02/1.21      inference('clc', [status(thm)], ['85', '86'])).
% 1.02/1.21  thf(fc7_struct_0, axiom,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 1.02/1.21       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 1.02/1.21  thf('88', plain,
% 1.02/1.21      (![X19 : $i]:
% 1.02/1.21         ((v1_zfmisc_1 @ (u1_struct_0 @ X19))
% 1.02/1.21          | ~ (l1_struct_0 @ X19)
% 1.02/1.21          | ~ (v7_struct_0 @ X19))),
% 1.02/1.21      inference('cnf', [status(esa)], [fc7_struct_0])).
% 1.02/1.21  thf('89', plain,
% 1.02/1.21      (((v1_zfmisc_1 @ sk_B_1)
% 1.02/1.21        | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.02/1.21        | ~ (l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 1.02/1.21      inference('sup+', [status(thm)], ['87', '88'])).
% 1.02/1.21  thf('90', plain,
% 1.02/1.21      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('91', plain,
% 1.02/1.21      (![X28 : $i, X29 : $i]:
% 1.02/1.21         ((v1_xboole_0 @ X28)
% 1.02/1.21          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 1.02/1.21          | (m1_pre_topc @ (sk_C_1 @ X28 @ X29) @ X29)
% 1.02/1.21          | ~ (l1_pre_topc @ X29)
% 1.02/1.21          | (v2_struct_0 @ X29))),
% 1.02/1.21      inference('cnf', [status(esa)], [t10_tsep_1])).
% 1.02/1.21  thf('92', plain,
% 1.02/1.21      (((v2_struct_0 @ sk_A)
% 1.02/1.21        | ~ (l1_pre_topc @ sk_A)
% 1.02/1.21        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 1.02/1.21        | (v1_xboole_0 @ sk_B_1))),
% 1.02/1.21      inference('sup-', [status(thm)], ['90', '91'])).
% 1.02/1.21  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('94', plain,
% 1.02/1.21      (((v2_struct_0 @ sk_A)
% 1.02/1.21        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 1.02/1.21        | (v1_xboole_0 @ sk_B_1))),
% 1.02/1.21      inference('demod', [status(thm)], ['92', '93'])).
% 1.02/1.21  thf('95', plain, (~ (v2_struct_0 @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('96', plain,
% 1.02/1.21      (((v1_xboole_0 @ sk_B_1)
% 1.02/1.21        | (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A))),
% 1.02/1.21      inference('clc', [status(thm)], ['94', '95'])).
% 1.02/1.21  thf('97', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('98', plain, ((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)),
% 1.02/1.21      inference('clc', [status(thm)], ['96', '97'])).
% 1.02/1.21  thf(dt_m1_pre_topc, axiom,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( l1_pre_topc @ A ) =>
% 1.02/1.21       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.02/1.21  thf('99', plain,
% 1.02/1.21      (![X17 : $i, X18 : $i]:
% 1.02/1.21         (~ (m1_pre_topc @ X17 @ X18)
% 1.02/1.21          | (l1_pre_topc @ X17)
% 1.02/1.21          | ~ (l1_pre_topc @ X18))),
% 1.02/1.21      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.02/1.21  thf('100', plain,
% 1.02/1.21      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['98', '99'])).
% 1.02/1.21  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('102', plain, ((l1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 1.02/1.21      inference('demod', [status(thm)], ['100', '101'])).
% 1.02/1.21  thf(dt_l1_pre_topc, axiom,
% 1.02/1.21    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.02/1.21  thf('103', plain,
% 1.02/1.21      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 1.02/1.21      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.02/1.21  thf('104', plain, ((l1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 1.02/1.21      inference('sup-', [status(thm)], ['102', '103'])).
% 1.02/1.21  thf('105', plain,
% 1.02/1.21      (((v1_zfmisc_1 @ sk_B_1) | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 1.02/1.21      inference('demod', [status(thm)], ['89', '104'])).
% 1.02/1.21  thf('106', plain, ((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)),
% 1.02/1.21      inference('clc', [status(thm)], ['96', '97'])).
% 1.02/1.21  thf(cc32_tex_2, axiom,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 1.02/1.21         ( l1_pre_topc @ A ) ) =>
% 1.02/1.21       ( ![B:$i]:
% 1.02/1.21         ( ( m1_pre_topc @ B @ A ) =>
% 1.02/1.21           ( ( ( ~( v2_struct_0 @ B ) ) & ( ~( v7_struct_0 @ B ) ) ) =>
% 1.02/1.21             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tdlat_3 @ B ) ) ) ) ) ) ))).
% 1.02/1.21  thf('107', plain,
% 1.02/1.21      (![X24 : $i, X25 : $i]:
% 1.02/1.21         (~ (m1_pre_topc @ X24 @ X25)
% 1.02/1.21          | ~ (v1_tdlat_3 @ X24)
% 1.02/1.21          | (v7_struct_0 @ X24)
% 1.02/1.21          | (v2_struct_0 @ X24)
% 1.02/1.21          | ~ (l1_pre_topc @ X25)
% 1.02/1.21          | ~ (v2_tdlat_3 @ X25)
% 1.02/1.21          | ~ (v2_pre_topc @ X25)
% 1.02/1.21          | (v2_struct_0 @ X25))),
% 1.02/1.21      inference('cnf', [status(esa)], [cc32_tex_2])).
% 1.02/1.21  thf('108', plain,
% 1.02/1.21      (((v2_struct_0 @ sk_A)
% 1.02/1.21        | ~ (v2_pre_topc @ sk_A)
% 1.02/1.21        | ~ (v2_tdlat_3 @ sk_A)
% 1.02/1.21        | ~ (l1_pre_topc @ sk_A)
% 1.02/1.21        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.02/1.21        | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.02/1.21        | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['106', '107'])).
% 1.02/1.21  thf('109', plain, ((v2_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('110', plain, ((v2_tdlat_3 @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('111', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('112', plain,
% 1.02/1.21      (((v2_struct_0 @ sk_A)
% 1.02/1.21        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.02/1.21        | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.02/1.21        | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 1.02/1.21      inference('demod', [status(thm)], ['108', '109', '110', '111'])).
% 1.02/1.21  thf('113', plain,
% 1.02/1.21      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('114', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 1.02/1.21      inference('clc', [status(thm)], ['85', '86'])).
% 1.02/1.21  thf(t26_tex_2, axiom,
% 1.02/1.21    (![A:$i]:
% 1.02/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.02/1.21       ( ![B:$i]:
% 1.02/1.21         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 1.02/1.21           ( ![C:$i]:
% 1.02/1.21             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.02/1.21               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 1.02/1.21                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 1.02/1.21  thf('115', plain,
% 1.02/1.21      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.02/1.21         ((v2_struct_0 @ X30)
% 1.02/1.21          | ~ (m1_pre_topc @ X30 @ X31)
% 1.02/1.21          | ((X32) != (u1_struct_0 @ X30))
% 1.02/1.21          | ~ (v2_tex_2 @ X32 @ X31)
% 1.02/1.21          | (v1_tdlat_3 @ X30)
% 1.02/1.21          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.02/1.21          | ~ (l1_pre_topc @ X31)
% 1.02/1.21          | (v2_struct_0 @ X31))),
% 1.02/1.21      inference('cnf', [status(esa)], [t26_tex_2])).
% 1.02/1.21  thf('116', plain,
% 1.02/1.21      (![X30 : $i, X31 : $i]:
% 1.02/1.21         ((v2_struct_0 @ X31)
% 1.02/1.21          | ~ (l1_pre_topc @ X31)
% 1.02/1.21          | ~ (m1_subset_1 @ (u1_struct_0 @ X30) @ 
% 1.02/1.21               (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.02/1.21          | (v1_tdlat_3 @ X30)
% 1.02/1.21          | ~ (v2_tex_2 @ (u1_struct_0 @ X30) @ X31)
% 1.02/1.21          | ~ (m1_pre_topc @ X30 @ X31)
% 1.02/1.21          | (v2_struct_0 @ X30))),
% 1.02/1.21      inference('simplify', [status(thm)], ['115'])).
% 1.02/1.21  thf('117', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.02/1.21          | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.02/1.21          | ~ (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ X0)
% 1.02/1.21          | ~ (v2_tex_2 @ (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)) @ X0)
% 1.02/1.21          | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.02/1.21          | ~ (l1_pre_topc @ X0)
% 1.02/1.21          | (v2_struct_0 @ X0))),
% 1.02/1.21      inference('sup-', [status(thm)], ['114', '116'])).
% 1.02/1.21  thf('118', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 1.02/1.21      inference('clc', [status(thm)], ['85', '86'])).
% 1.02/1.21  thf('119', plain,
% 1.02/1.21      (![X0 : $i]:
% 1.02/1.21         (~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.02/1.21          | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.02/1.21          | ~ (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ X0)
% 1.02/1.21          | ~ (v2_tex_2 @ sk_B_1 @ X0)
% 1.02/1.21          | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.02/1.21          | ~ (l1_pre_topc @ X0)
% 1.02/1.21          | (v2_struct_0 @ X0))),
% 1.02/1.21      inference('demod', [status(thm)], ['117', '118'])).
% 1.02/1.21  thf('120', plain,
% 1.02/1.21      (((v2_struct_0 @ sk_A)
% 1.02/1.21        | ~ (l1_pre_topc @ sk_A)
% 1.02/1.21        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.02/1.21        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 1.02/1.21        | ~ (m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)
% 1.02/1.21        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 1.02/1.21      inference('sup-', [status(thm)], ['113', '119'])).
% 1.02/1.21  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('122', plain,
% 1.02/1.21      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.02/1.21      inference('split', [status(esa)], ['10'])).
% 1.02/1.21  thf('123', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ((v1_zfmisc_1 @ sk_B_1))),
% 1.02/1.21      inference('split', [status(esa)], ['10'])).
% 1.02/1.21  thf('124', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.02/1.21      inference('sat_resolution*', [status(thm)], ['2', '76', '123'])).
% 1.02/1.21  thf('125', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 1.02/1.21      inference('simpl_trail', [status(thm)], ['122', '124'])).
% 1.02/1.21  thf('126', plain, ((m1_pre_topc @ (sk_C_1 @ sk_B_1 @ sk_A) @ sk_A)),
% 1.02/1.21      inference('clc', [status(thm)], ['96', '97'])).
% 1.02/1.21  thf('127', plain,
% 1.02/1.21      (((v2_struct_0 @ sk_A)
% 1.02/1.21        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.02/1.21        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 1.02/1.21      inference('demod', [status(thm)], ['120', '121', '125', '126'])).
% 1.02/1.21  thf('128', plain, (~ (v2_struct_0 @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('129', plain,
% 1.02/1.21      (((v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.02/1.21        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 1.02/1.21      inference('clc', [status(thm)], ['127', '128'])).
% 1.02/1.21  thf('130', plain,
% 1.02/1.21      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('131', plain,
% 1.02/1.21      (![X28 : $i, X29 : $i]:
% 1.02/1.21         ((v1_xboole_0 @ X28)
% 1.02/1.21          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 1.02/1.21          | ~ (v2_struct_0 @ (sk_C_1 @ X28 @ X29))
% 1.02/1.21          | ~ (l1_pre_topc @ X29)
% 1.02/1.21          | (v2_struct_0 @ X29))),
% 1.02/1.21      inference('cnf', [status(esa)], [t10_tsep_1])).
% 1.02/1.21  thf('132', plain,
% 1.02/1.21      (((v2_struct_0 @ sk_A)
% 1.02/1.21        | ~ (l1_pre_topc @ sk_A)
% 1.02/1.21        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.02/1.21        | (v1_xboole_0 @ sk_B_1))),
% 1.02/1.21      inference('sup-', [status(thm)], ['130', '131'])).
% 1.02/1.21  thf('133', plain, ((l1_pre_topc @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('134', plain,
% 1.02/1.21      (((v2_struct_0 @ sk_A)
% 1.02/1.21        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.02/1.21        | (v1_xboole_0 @ sk_B_1))),
% 1.02/1.21      inference('demod', [status(thm)], ['132', '133'])).
% 1.02/1.21  thf('135', plain, (~ (v2_struct_0 @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('136', plain,
% 1.02/1.21      (((v1_xboole_0 @ sk_B_1) | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 1.02/1.21      inference('clc', [status(thm)], ['134', '135'])).
% 1.02/1.21  thf('137', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('138', plain, (~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 1.02/1.21      inference('clc', [status(thm)], ['136', '137'])).
% 1.02/1.21  thf('139', plain, ((v1_tdlat_3 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 1.02/1.21      inference('clc', [status(thm)], ['129', '138'])).
% 1.02/1.21  thf('140', plain,
% 1.02/1.21      (((v2_struct_0 @ sk_A)
% 1.02/1.21        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.02/1.21        | (v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 1.02/1.21      inference('demod', [status(thm)], ['112', '139'])).
% 1.02/1.21  thf('141', plain, (~ (v2_struct_0 @ sk_A)),
% 1.02/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.21  thf('142', plain,
% 1.02/1.21      (((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))
% 1.02/1.21        | (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A)))),
% 1.02/1.21      inference('clc', [status(thm)], ['140', '141'])).
% 1.02/1.21  thf('143', plain, (~ (v2_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 1.02/1.21      inference('clc', [status(thm)], ['136', '137'])).
% 1.02/1.21  thf('144', plain, ((v7_struct_0 @ (sk_C_1 @ sk_B_1 @ sk_A))),
% 1.02/1.21      inference('clc', [status(thm)], ['142', '143'])).
% 1.02/1.21  thf('145', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 1.02/1.21      inference('demod', [status(thm)], ['105', '144'])).
% 1.02/1.21  thf('146', plain, ($false), inference('demod', [status(thm)], ['78', '145'])).
% 1.02/1.21  
% 1.02/1.21  % SZS output end Refutation
% 1.02/1.21  
% 1.02/1.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
