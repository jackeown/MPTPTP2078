%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FXeglhCToh

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 190 expanded)
%              Number of leaves         :   27 (  66 expanded)
%              Depth                    :   19
%              Number of atoms          :  689 (2146 expanded)
%              Number of equality atoms :   16 (  68 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t14_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
                    = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
                  & ( v1_tex_2 @ B @ A ) )
               => ( v1_tex_2 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_pre_topc @ B @ A )
           => ! [C: $i] :
                ( ( m1_pre_topc @ C @ A )
               => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
                      = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) )
                    & ( v1_tex_2 @ B @ A ) )
                 => ( v1_tex_2 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_tex_2])).

thf('0',plain,(
    ~ ( v1_tex_2 @ sk_C_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('2',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( ( sk_C_1 @ X22 @ X23 )
        = ( u1_struct_0 @ X22 ) )
      | ( v1_tex_2 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_C_2 @ sk_A )
    | ( ( sk_C_1 @ sk_C_2 @ sk_A )
      = ( u1_struct_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('5',plain,(
    ! [X21: $i] :
      ( ( m1_pre_topc @ X21 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ( m1_pre_topc @ X18 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_pre_topc @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) )
      | ( m1_pre_topc @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ~ ( l1_pre_topc @ sk_C_2 )
      | ( m1_pre_topc @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_pre_topc @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
      | ( m1_pre_topc @ X0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_pre_topc @ sk_B @ sk_C_2 ),
    inference(demod,[status(thm)],['18','23'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('25',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_C_2 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['14','15'])).

thf('28',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_2 ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('31',plain,(
    ! [X9: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('32',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('33',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r1_tarski @ X6 @ X4 )
      | ( X5
       != ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('34',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_C_2 )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_pre_topc @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('40',plain,
    ( ( m1_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['14','15'])).

thf('42',plain,(
    m1_pre_topc @ sk_C_2 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) )
      | ( m1_pre_topc @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_pre_topc @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('46',plain,(
    m1_pre_topc @ sk_C_2 @ sk_B ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('48',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['21','22'])).

thf('50',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X9: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('54',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('56',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( u1_struct_0 @ sk_C_2 )
    = ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['37','56'])).

thf('58',plain,
    ( ( v1_tex_2 @ sk_C_2 @ sk_A )
    | ( ( sk_C_1 @ sk_C_2 @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['3','4','57'])).

thf('59',plain,(
    ~ ( v1_tex_2 @ sk_C_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( sk_C_1 @ sk_C_2 @ sk_A )
    = ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( v1_subset_1 @ ( sk_C_1 @ X22 @ X23 ) @ ( u1_struct_0 @ X23 ) )
      | ( v1_tex_2 @ X22 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('62',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_C_2 @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('65',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( v1_tex_2 @ X22 @ X23 )
      | ( X24
       != ( u1_struct_0 @ X22 ) )
      | ( v1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('69',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( v1_tex_2 @ X22 @ X23 )
      | ~ ( m1_pre_topc @ X22 @ X23 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tex_2 @ sk_B @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['67','69'])).

thf('71',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_pre_topc @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_tex_2 @ sk_C_2 @ sk_A ),
    inference(demod,[status(thm)],['62','74','75','76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['0','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FXeglhCToh
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:39:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 142 iterations in 0.065s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.20/0.52  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.52  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(t14_tex_2, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.52               ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.20/0.52                     ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) & 
% 0.20/0.52                   ( v1_tex_2 @ B @ A ) ) =>
% 0.20/0.52                 ( v1_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( l1_pre_topc @ A ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.52              ( ![C:$i]:
% 0.20/0.52                ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.52                  ( ( ( ( g1_pre_topc @
% 0.20/0.52                          ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) =
% 0.20/0.52                        ( g1_pre_topc @
% 0.20/0.52                          ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) & 
% 0.20/0.52                      ( v1_tex_2 @ B @ A ) ) =>
% 0.20/0.52                    ( v1_tex_2 @ C @ A ) ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t14_tex_2])).
% 0.20/0.52  thf('0', plain, (~ (v1_tex_2 @ sk_C_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('1', plain, ((m1_pre_topc @ sk_C_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d3_tex_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.52           ( ( v1_tex_2 @ B @ A ) <=>
% 0.20/0.52             ( ![C:$i]:
% 0.20/0.52               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.52                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X22 : $i, X23 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X22 @ X23)
% 0.20/0.52          | ((sk_C_1 @ X22 @ X23) = (u1_struct_0 @ X22))
% 0.20/0.52          | (v1_tex_2 @ X22 @ X23)
% 0.20/0.52          | ~ (l1_pre_topc @ X23))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (v1_tex_2 @ sk_C_2 @ sk_A)
% 0.20/0.52        | ((sk_C_1 @ sk_C_2 @ sk_A) = (u1_struct_0 @ sk_C_2)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t2_tsep_1, axiom,
% 0.20/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X21 : $i]: ((m1_pre_topc @ X21 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.20/0.52      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.20/0.52  thf(t65_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( l1_pre_topc @ B ) =>
% 0.20/0.52           ( ( m1_pre_topc @ A @ B ) <=>
% 0.20/0.52             ( m1_pre_topc @
% 0.20/0.52               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X17)
% 0.20/0.52          | ~ (m1_pre_topc @ X18 @ X17)
% 0.20/0.52          | (m1_pre_topc @ X18 @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)))
% 0.20/0.52          | ~ (l1_pre_topc @ X18))),
% 0.20/0.52      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X0)
% 0.20/0.52          | ~ (l1_pre_topc @ X0)
% 0.20/0.52          | (m1_pre_topc @ X0 @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.52          | ~ (l1_pre_topc @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_pre_topc @ X0 @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.52          | ~ (l1_pre_topc @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.20/0.52         = (g1_pre_topc @ (u1_struct_0 @ sk_C_2) @ (u1_pre_topc @ sk_C_2)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t59_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_pre_topc @
% 0.20/0.52             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.20/0.52           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X15 @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)))
% 0.20/0.52          | (m1_pre_topc @ X15 @ X16)
% 0.20/0.52          | ~ (l1_pre_topc @ X16))),
% 0.20/0.52      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X0 @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52          | ~ (l1_pre_topc @ sk_C_2)
% 0.20/0.52          | (m1_pre_topc @ X0 @ sk_C_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.52  thf('12', plain, ((m1_pre_topc @ sk_C_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_m1_pre_topc, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X13 @ X14)
% 0.20/0.52          | (l1_pre_topc @ X13)
% 0.20/0.52          | ~ (l1_pre_topc @ X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.52  thf('14', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.52  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('16', plain, ((l1_pre_topc @ sk_C_2)),
% 0.20/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X0 @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52          | (m1_pre_topc @ X0 @ sk_C_2))),
% 0.20/0.52      inference('demod', [status(thm)], ['11', '16'])).
% 0.20/0.52  thf('18', plain, ((~ (l1_pre_topc @ sk_B) | (m1_pre_topc @ sk_B @ sk_C_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['8', '17'])).
% 0.20/0.52  thf('19', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X13 : $i, X14 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X13 @ X14)
% 0.20/0.52          | (l1_pre_topc @ X13)
% 0.20/0.52          | ~ (l1_pre_topc @ X14))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.52  thf('21', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('23', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.52      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.52  thf('24', plain, ((m1_pre_topc @ sk_B @ sk_C_2)),
% 0.20/0.52      inference('demod', [status(thm)], ['18', '23'])).
% 0.20/0.52  thf(t1_tsep_1, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_pre_topc @ A ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.52           ( m1_subset_1 @
% 0.20/0.52             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      (![X19 : $i, X20 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X19 @ X20)
% 0.20/0.52          | (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.20/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.20/0.52          | ~ (l1_pre_topc @ X20))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_C_2)
% 0.20/0.52        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_2))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.52  thf('27', plain, ((l1_pre_topc @ sk_C_2)),
% 0.20/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_2)))),
% 0.20/0.52      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf(t2_subset, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.52       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (![X11 : $i, X12 : $i]:
% 0.20/0.52         ((r2_hidden @ X11 @ X12)
% 0.20/0.52          | (v1_xboole_0 @ X12)
% 0.20/0.52          | ~ (m1_subset_1 @ X11 @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_2)))
% 0.20/0.52        | (r2_hidden @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_2))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.52  thf(fc1_subset_1, axiom,
% 0.20/0.52    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.52  thf('31', plain, (![X9 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      ((r2_hidden @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_2)))),
% 0.20/0.52      inference('clc', [status(thm)], ['30', '31'])).
% 0.20/0.52  thf(d1_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X6 @ X5)
% 0.20/0.52          | (r1_tarski @ X6 @ X4)
% 0.20/0.52          | ((X5) != (k1_zfmisc_1 @ X4)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (![X4 : $i, X6 : $i]:
% 0.20/0.52         ((r1_tarski @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['32', '34'])).
% 0.20/0.52  thf(d10_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (![X0 : $i, X2 : $i]:
% 0.20/0.52         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      ((~ (r1_tarski @ (u1_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_B))
% 0.20/0.52        | ((u1_struct_0 @ sk_C_2) = (u1_struct_0 @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (((g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B))
% 0.20/0.52         = (g1_pre_topc @ (u1_struct_0 @ sk_C_2) @ (u1_pre_topc @ sk_C_2)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_pre_topc @ X0 @ 
% 0.20/0.52           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.52          | ~ (l1_pre_topc @ X0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (((m1_pre_topc @ sk_C_2 @ 
% 0.20/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))
% 0.20/0.52        | ~ (l1_pre_topc @ sk_C_2))),
% 0.20/0.52      inference('sup+', [status(thm)], ['38', '39'])).
% 0.20/0.52  thf('41', plain, ((l1_pre_topc @ sk_C_2)),
% 0.20/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      ((m1_pre_topc @ sk_C_2 @ 
% 0.20/0.52        (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (![X15 : $i, X16 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X15 @ 
% 0.20/0.52             (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)))
% 0.20/0.52          | (m1_pre_topc @ X15 @ X16)
% 0.20/0.52          | ~ (l1_pre_topc @ X16))),
% 0.20/0.52      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.20/0.52  thf('44', plain, ((~ (l1_pre_topc @ sk_B) | (m1_pre_topc @ sk_C_2 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.52  thf('45', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.52      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.52  thf('46', plain, ((m1_pre_topc @ sk_C_2 @ sk_B)),
% 0.20/0.52      inference('demod', [status(thm)], ['44', '45'])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (![X19 : $i, X20 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X19 @ X20)
% 0.20/0.52          | (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.20/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.20/0.52          | ~ (l1_pre_topc @ X20))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_B)
% 0.20/0.52        | (m1_subset_1 @ (u1_struct_0 @ sk_C_2) @ 
% 0.20/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.52  thf('49', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.52      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      ((m1_subset_1 @ (u1_struct_0 @ sk_C_2) @ 
% 0.20/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['48', '49'])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      (![X11 : $i, X12 : $i]:
% 0.20/0.52         ((r2_hidden @ X11 @ X12)
% 0.20/0.52          | (v1_xboole_0 @ X12)
% 0.20/0.52          | ~ (m1_subset_1 @ X11 @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.20/0.52        | (r2_hidden @ (u1_struct_0 @ sk_C_2) @ 
% 0.20/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.52  thf('53', plain, (![X9 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      ((r2_hidden @ (u1_struct_0 @ sk_C_2) @ 
% 0.20/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.52      inference('clc', [status(thm)], ['52', '53'])).
% 0.20/0.52  thf('55', plain,
% 0.20/0.52      (![X4 : $i, X6 : $i]:
% 0.20/0.52         ((r1_tarski @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.52  thf('56', plain,
% 0.20/0.52      ((r1_tarski @ (u1_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.52  thf('57', plain, (((u1_struct_0 @ sk_C_2) = (u1_struct_0 @ sk_B))),
% 0.20/0.52      inference('demod', [status(thm)], ['37', '56'])).
% 0.20/0.52  thf('58', plain,
% 0.20/0.52      (((v1_tex_2 @ sk_C_2 @ sk_A)
% 0.20/0.52        | ((sk_C_1 @ sk_C_2 @ sk_A) = (u1_struct_0 @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['3', '4', '57'])).
% 0.20/0.52  thf('59', plain, (~ (v1_tex_2 @ sk_C_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('60', plain, (((sk_C_1 @ sk_C_2 @ sk_A) = (u1_struct_0 @ sk_B))),
% 0.20/0.52      inference('clc', [status(thm)], ['58', '59'])).
% 0.20/0.52  thf('61', plain,
% 0.20/0.52      (![X22 : $i, X23 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X22 @ X23)
% 0.20/0.52          | ~ (v1_subset_1 @ (sk_C_1 @ X22 @ X23) @ (u1_struct_0 @ X23))
% 0.20/0.52          | (v1_tex_2 @ X22 @ X23)
% 0.20/0.52          | ~ (l1_pre_topc @ X23))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.20/0.52  thf('62', plain,
% 0.20/0.52      ((~ (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (v1_tex_2 @ sk_C_2 @ sk_A)
% 0.20/0.52        | ~ (m1_pre_topc @ sk_C_2 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.52  thf('63', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('64', plain,
% 0.20/0.52      (![X19 : $i, X20 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X19 @ X20)
% 0.20/0.52          | (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.20/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.20/0.52          | ~ (l1_pre_topc @ X20))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.52  thf('65', plain,
% 0.20/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.52        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.52  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('67', plain,
% 0.20/0.52      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.52  thf('68', plain,
% 0.20/0.52      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.52         (~ (m1_pre_topc @ X22 @ X23)
% 0.20/0.52          | ~ (v1_tex_2 @ X22 @ X23)
% 0.20/0.52          | ((X24) != (u1_struct_0 @ X22))
% 0.20/0.52          | (v1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.20/0.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.20/0.52          | ~ (l1_pre_topc @ X23))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.20/0.52  thf('69', plain,
% 0.20/0.52      (![X22 : $i, X23 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X23)
% 0.20/0.52          | ~ (m1_subset_1 @ (u1_struct_0 @ X22) @ 
% 0.20/0.52               (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.20/0.52          | (v1_subset_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))
% 0.20/0.52          | ~ (v1_tex_2 @ X22 @ X23)
% 0.20/0.52          | ~ (m1_pre_topc @ X22 @ X23))),
% 0.20/0.52      inference('simplify', [status(thm)], ['68'])).
% 0.20/0.52  thf('70', plain,
% 0.20/0.52      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 0.20/0.52        | ~ (v1_tex_2 @ sk_B @ sk_A)
% 0.20/0.52        | (v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['67', '69'])).
% 0.20/0.52  thf('71', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('72', plain, ((v1_tex_2 @ sk_B @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('74', plain,
% 0.20/0.52      ((v1_subset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 0.20/0.52  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('76', plain, ((m1_pre_topc @ sk_C_2 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('77', plain, ((v1_tex_2 @ sk_C_2 @ sk_A)),
% 0.20/0.52      inference('demod', [status(thm)], ['62', '74', '75', '76'])).
% 0.20/0.52  thf('78', plain, ($false), inference('demod', [status(thm)], ['0', '77'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
