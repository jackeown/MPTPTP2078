%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1855+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NsAevfpaqA

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:25 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :  258 (8618 expanded)
%              Number of leaves         :   35 (2506 expanded)
%              Depth                    :   51
%              Number of atoms          : 2730 (117883 expanded)
%              Number of equality atoms :   88 (3688 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t23_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v7_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ? [C: $i] :
              ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
                = ( g1_pre_topc @ ( u1_struct_0 @ ( k1_tex_2 @ A @ C ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ A @ C ) ) ) )
              & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v7_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ? [C: $i] :
                ( ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
                  = ( g1_pre_topc @ ( u1_struct_0 @ ( k1_tex_2 @ A @ C ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ A @ C ) ) ) )
                & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_tex_2])).

thf('0',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l17_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[l17_tex_2])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d1_tex_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( ( v7_struct_0 @ A )
      <=> ? [B: $i] :
            ( ( ( u1_struct_0 @ A )
              = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
            & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v7_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v7_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_1])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( ( k6_domain_1 @ X13 @ X14 )
        = ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ( ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('13',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t37_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ ( k1_tarski @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v7_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,(
    v7_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('25',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('26',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['18','19','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('30',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('31',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(dt_k1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) )
        & ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ) )).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X5 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('33',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( v1_pre_topc @ ( k1_tex_2 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('40',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf(d4_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( v1_pre_topc @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( C
                  = ( k1_tex_2 @ A @ B ) )
              <=> ( ( u1_struct_0 @ C )
                  = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('45',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X3 ) )
      | ( X4
       != ( k1_tex_2 @ X3 @ X2 ) )
      | ( ( u1_struct_0 @ X4 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X3 ) @ X2 ) )
      | ~ ( m1_pre_topc @ X4 @ X3 )
      | ~ ( v1_pre_topc @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d4_tex_2])).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X3 @ X2 ) )
      | ~ ( v1_pre_topc @ ( k1_tex_2 @ X3 @ X2 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X3 @ X2 ) @ X3 )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X3 @ X2 ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X3 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('52',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( ( k6_domain_1 @ X13 @ X14 )
        = ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('53',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['27','28'])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('55',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X31 @ X32 )
      | ~ ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('56',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['53','56'])).

thf('58',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['35','36'])).

thf('59',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','57','58'])).

thf('60',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('61',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('62',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['59','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf(t5_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( ( u1_struct_0 @ B )
                  = ( u1_struct_0 @ C ) )
               => ( ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) )
                  = ( g1_pre_topc @ ( u1_struct_0 @ C ) @ ( u1_pre_topc @ C ) ) ) ) ) ) ) )).

thf('70',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X28 @ X29 )
      | ( ( u1_struct_0 @ X28 )
       != ( u1_struct_0 @ X30 ) )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X28 ) @ ( u1_pre_topc @ X28 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ X30 ) @ ( u1_pre_topc @ X30 ) ) )
      | ~ ( m1_pre_topc @ X30 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t5_tsep_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( g1_pre_topc @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( v7_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_1])).

thf('75',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( v7_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v7_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v7_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_1])).

thf('79',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X5 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ( m1_pre_topc @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v7_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_1])).

thf('83',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( v1_pre_topc @ ( k1_tex_2 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ( v1_pre_topc @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X3 @ X2 ) )
      | ~ ( v1_pre_topc @ ( k1_tex_2 @ X3 @ X2 ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X3 @ X2 ) @ X3 )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X3 @ X2 ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X3 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ X0 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) @ X0 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) @ X0 )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['81','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ X0 ) ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['77','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('94',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[l17_tex_2])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['92','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r1_tarski @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['76','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v7_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_1])).

thf('104',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X0 @ ( sk_B @ X0 ) ) )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['75','108'])).

thf('110',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('111',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['35','36'])).

thf('112',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('113',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X7: $i] :
      ( ( l1_struct_0 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('117',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('119',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['109','110','117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('121',plain,
    ( ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ( ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v7_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('126',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
       != ( k6_domain_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('130',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('131',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
       != ( k6_domain_1 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['128','129','130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_B_1 )
      | ~ ( v7_struct_0 @ sk_B_1 )
      | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
       != ( k6_domain_1 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ X0 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['125','132'])).

thf('134',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('135',plain,(
    v7_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
       != ( k6_domain_1 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ X0 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
       != ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_B_1 )
      | ~ ( v7_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['124','136'])).

thf('138',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('139',plain,(
    v7_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
       != ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['137','138','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
       != ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ~ ( v7_struct_0 @ sk_B_1 )
    | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['123','141'])).

thf('143',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('144',plain,(
    v7_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,
    ( ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
     != ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( v7_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['122','146'])).

thf('148',plain,(
    v7_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('150',plain,
    ( ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
     != ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('153',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('155',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('156',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('157',plain,
    ( ~ ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('159',plain,
    ( ~ ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('161',plain,(
    ~ ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['159','160'])).

thf('162',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ~ ( v7_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['154','161'])).

thf('163',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('164',plain,(
    v7_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['162','163','164'])).

thf('166',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['153','167'])).

thf('169',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['168','169'])).

thf('171',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['121','170'])).

thf('172',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ ( k1_tarski @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('173',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X19 ) @ X21 )
      | ~ ( r2_hidden @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X22: $i,X24: $i] :
      ( ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('181',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('182',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ( m1_subset_1 @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( v7_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['173','183'])).

thf('185',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('186',plain,(
    v7_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('188',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['184','185','186','187'])).

thf('189',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( ( k6_domain_1 @ X13 @ X14 )
        = ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('192',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['165','166'])).

thf('194',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( sk_B @ sk_B_1 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['192','193'])).

thf('195',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ~ ( v7_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['74','194'])).

thf('196',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('197',plain,(
    v7_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('199',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['198','199'])).

thf('201',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['198','199'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ X0 )
       != ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) @ X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['73','200','201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( ( u1_struct_0 @ X0 )
       != ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['37','202'])).

thf('204',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
        = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) )
      | ( ( u1_struct_0 @ X0 )
       != ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['203','204'])).

thf('206',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
      = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A ) ),
    inference(eq_res,[status(thm)],['205'])).

thf('207',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('210',plain,
    ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('211',plain,(
    ! [X33: $i] :
      ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
       != ( g1_pre_topc @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ X33 ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ X33 ) ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
     != ( g1_pre_topc @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('214',plain,(
    ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
 != ( g1_pre_topc @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['212','213'])).

thf('215',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
     != ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ~ ( v7_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['209','214'])).

thf('216',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('217',plain,(
    v7_struct_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
     != ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['215','216','217'])).

thf('219',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
 != ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ ( k1_tex_2 @ sk_A @ ( sk_B @ sk_B_1 ) ) ) ) ),
    inference(clc,[status(thm)],['218','219'])).

thf('221',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['208','220'])).


%------------------------------------------------------------------------------
