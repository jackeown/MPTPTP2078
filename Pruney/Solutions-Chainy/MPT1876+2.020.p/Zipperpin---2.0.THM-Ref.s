%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G1nBopIfSe

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:58 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :  188 (1180 expanded)
%              Number of leaves         :   45 ( 352 expanded)
%              Depth                    :   31
%              Number of atoms          : 1185 (11832 expanded)
%              Number of equality atoms :   29 ( 293 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( ~ ( v2_struct_0 @ C )
                    & ( v1_pre_topc @ C )
                    & ( v1_tdlat_3 @ C )
                    & ( m1_pre_topc @ C @ A ) )
                 => ( B
                   != ( u1_struct_0 @ C ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X37: $i,X38: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( v2_tex_2 @ X37 @ X38 )
      | ~ ( v2_struct_0 @ ( sk_C @ X37 @ X38 ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('19',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('20',plain,
    ( sk_B_1
    = ( k3_xboole_0 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X5 )
      | ( X6
       != ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('22',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','23'])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('28',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X5 )
      | ( r2_hidden @ X3 @ X6 )
      | ( X6
       != ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('29',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X3 @ ( k3_xboole_0 @ X4 @ X5 ) )
      | ~ ( r2_hidden @ X3 @ X5 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('35',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X17 ) @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r2_hidden @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('37',plain,(
    m1_subset_1 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('40',plain,(
    ! [X35: $i,X36: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ~ ( v1_zfmisc_1 @ X35 )
      | ( X36 = X35 )
      | ~ ( r1_tarski @ X36 @ X35 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = sk_B_1 )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
        = sk_B_1 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','41'])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
      | ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
        = sk_B_1 ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['42','43'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('45',plain,(
    ! [X16: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('46',plain,
    ( ( ( k1_tarski @ ( sk_B @ sk_B_1 ) )
      = sk_B_1 )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('48',plain,(
    ! [X21: $i,X22: $i] :
      ( ( m1_subset_1 @ X21 @ X22 )
      | ~ ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('49',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('50',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( u1_struct_0 @ X40 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X40 ) @ X39 ) @ X40 )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('56',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ X30 )
      | ( ( k6_domain_1 @ X30 @ X31 )
        = ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('57',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('59',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( v1_xboole_0 @ X19 )
      | ~ ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('60',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['57','62'])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['54','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['46','66'])).

thf('68',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('69',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('71',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['9','69','70'])).

thf('72',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','71'])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X37: $i,X38: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( v2_tex_2 @ X37 @ X38 )
      | ( m1_pre_topc @ ( sk_C @ X37 @ X38 ) @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','71'])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['87','88'])).

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

thf('90',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_pre_topc @ X33 @ X34 )
      | ~ ( v1_tdlat_3 @ X33 )
      | ( v7_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_tdlat_3 @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[cc32_tex_2])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('96',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X37: $i,X38: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( v2_tex_2 @ X37 @ X38 )
      | ( v1_tdlat_3 @ ( sk_C @ X37 @ X38 ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['98','99','100'])).

thf('102',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['95','101'])).

thf('103',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['9','69','70'])).

thf('108',plain,(
    v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['91','92','93','94','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('113',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X37: $i,X38: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( v2_tex_2 @ X37 @ X38 )
      | ( X37
        = ( u1_struct_0 @ ( sk_C @ X37 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf('119',plain,
    ( ( ( v1_xboole_0 @ sk_B_1 )
      | ( sk_B_1
        = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['112','118'])).

thf('120',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( sk_B_1
        = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['121','122'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('124',plain,(
    ! [X29: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 )
      | ~ ( v7_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('125',plain,
    ( ( ( v1_zfmisc_1 @ sk_B_1 )
      | ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
      | ~ ( l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['9','69','70'])).

thf('127',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['125','126'])).

thf('128',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
   <= ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('129',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['9','69'])).

thf('130',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['128','129'])).

thf('131',plain,
    ( ~ ( l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['127','130'])).

thf('132',plain,(
    m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['87','88'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('133',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( l1_pre_topc @ X27 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('134',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['134','135'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('137',plain,(
    ! [X26: $i] :
      ( ( l1_struct_0 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('138',plain,(
    l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['131','138'])).

thf('140',plain,(
    v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['111','139'])).

thf('141',plain,(
    $false ),
    inference(demod,[status(thm)],['77','140'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G1nBopIfSe
% 0.14/0.37  % Computer   : n016.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 11:46:49 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 1.69/1.91  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.69/1.91  % Solved by: fo/fo7.sh
% 1.69/1.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.69/1.91  % done 1161 iterations in 1.426s
% 1.69/1.91  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.69/1.91  % SZS output start Refutation
% 1.69/1.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.69/1.91  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.69/1.91  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 1.69/1.91  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.69/1.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.69/1.91  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 1.69/1.91  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.69/1.91  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.69/1.91  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 1.69/1.91  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.69/1.91  thf(sk_A_type, type, sk_A: $i).
% 1.69/1.91  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.69/1.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.69/1.91  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.69/1.91  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.69/1.91  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.69/1.91  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.69/1.91  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.69/1.91  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 1.69/1.91  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.69/1.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.69/1.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.69/1.91  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 1.69/1.91  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.69/1.91  thf(sk_B_type, type, sk_B: $i > $i).
% 1.69/1.91  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 1.69/1.91  thf(t44_tex_2, conjecture,
% 1.69/1.91    (![A:$i]:
% 1.69/1.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 1.69/1.91         ( l1_pre_topc @ A ) ) =>
% 1.69/1.91       ( ![B:$i]:
% 1.69/1.91         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.69/1.91             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.69/1.91           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 1.69/1.91  thf(zf_stmt_0, negated_conjecture,
% 1.69/1.91    (~( ![A:$i]:
% 1.69/1.91        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.69/1.91            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.69/1.91          ( ![B:$i]:
% 1.69/1.91            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.69/1.91                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.69/1.91              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 1.69/1.91    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 1.69/1.91  thf('0', plain,
% 1.69/1.91      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf(t34_tex_2, axiom,
% 1.69/1.91    (![A:$i]:
% 1.69/1.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.69/1.91       ( ![B:$i]:
% 1.69/1.91         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 1.69/1.91             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.69/1.91           ( ~( ( v2_tex_2 @ B @ A ) & 
% 1.69/1.91                ( ![C:$i]:
% 1.69/1.91                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 1.69/1.91                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.69/1.91                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 1.69/1.91  thf('1', plain,
% 1.69/1.91      (![X37 : $i, X38 : $i]:
% 1.69/1.91         ((v1_xboole_0 @ X37)
% 1.69/1.91          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 1.69/1.91          | ~ (v2_tex_2 @ X37 @ X38)
% 1.69/1.91          | ~ (v2_struct_0 @ (sk_C @ X37 @ X38))
% 1.69/1.91          | ~ (l1_pre_topc @ X38)
% 1.69/1.91          | ~ (v2_pre_topc @ X38)
% 1.69/1.91          | (v2_struct_0 @ X38))),
% 1.69/1.91      inference('cnf', [status(esa)], [t34_tex_2])).
% 1.69/1.91  thf('2', plain,
% 1.69/1.91      (((v2_struct_0 @ sk_A)
% 1.69/1.91        | ~ (v2_pre_topc @ sk_A)
% 1.69/1.91        | ~ (l1_pre_topc @ sk_A)
% 1.69/1.91        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 1.69/1.91        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 1.69/1.91        | (v1_xboole_0 @ sk_B_1))),
% 1.69/1.91      inference('sup-', [status(thm)], ['0', '1'])).
% 1.69/1.91  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('5', plain,
% 1.69/1.91      (((v2_struct_0 @ sk_A)
% 1.69/1.91        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 1.69/1.91        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 1.69/1.91        | (v1_xboole_0 @ sk_B_1))),
% 1.69/1.91      inference('demod', [status(thm)], ['2', '3', '4'])).
% 1.69/1.91  thf('6', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('7', plain,
% 1.69/1.91      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.69/1.91      inference('split', [status(esa)], ['6'])).
% 1.69/1.91  thf('8', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('9', plain,
% 1.69/1.91      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.69/1.91      inference('split', [status(esa)], ['8'])).
% 1.69/1.91  thf('10', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.69/1.91      inference('split', [status(esa)], ['6'])).
% 1.69/1.91  thf(d1_xboole_0, axiom,
% 1.69/1.91    (![A:$i]:
% 1.69/1.91     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.69/1.91  thf('11', plain,
% 1.69/1.91      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.69/1.91      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.69/1.91  thf('12', plain,
% 1.69/1.91      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf(t3_subset, axiom,
% 1.69/1.91    (![A:$i,B:$i]:
% 1.69/1.91     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.69/1.91  thf('13', plain,
% 1.69/1.91      (![X23 : $i, X24 : $i]:
% 1.69/1.91         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 1.69/1.91      inference('cnf', [status(esa)], [t3_subset])).
% 1.69/1.91  thf('14', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 1.69/1.91      inference('sup-', [status(thm)], ['12', '13'])).
% 1.69/1.91  thf(l32_xboole_1, axiom,
% 1.69/1.91    (![A:$i,B:$i]:
% 1.69/1.91     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.69/1.91  thf('15', plain,
% 1.69/1.91      (![X9 : $i, X11 : $i]:
% 1.69/1.91         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 1.69/1.91      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.69/1.91  thf('16', plain,
% 1.69/1.91      (((k4_xboole_0 @ sk_B_1 @ (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 1.69/1.91      inference('sup-', [status(thm)], ['14', '15'])).
% 1.69/1.91  thf(t48_xboole_1, axiom,
% 1.69/1.91    (![A:$i,B:$i]:
% 1.69/1.91     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.69/1.91  thf('17', plain,
% 1.69/1.91      (![X13 : $i, X14 : $i]:
% 1.69/1.91         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 1.69/1.91           = (k3_xboole_0 @ X13 @ X14))),
% 1.69/1.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.69/1.91  thf('18', plain,
% 1.69/1.91      (((k4_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 1.69/1.91         = (k3_xboole_0 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 1.69/1.91      inference('sup+', [status(thm)], ['16', '17'])).
% 1.69/1.91  thf(t3_boole, axiom,
% 1.69/1.91    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.69/1.91  thf('19', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 1.69/1.91      inference('cnf', [status(esa)], [t3_boole])).
% 1.69/1.91  thf('20', plain,
% 1.69/1.91      (((sk_B_1) = (k3_xboole_0 @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 1.69/1.91      inference('demod', [status(thm)], ['18', '19'])).
% 1.69/1.91  thf(d4_xboole_0, axiom,
% 1.69/1.91    (![A:$i,B:$i,C:$i]:
% 1.69/1.91     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.69/1.91       ( ![D:$i]:
% 1.69/1.91         ( ( r2_hidden @ D @ C ) <=>
% 1.69/1.91           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.69/1.91  thf('21', plain,
% 1.69/1.91      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 1.69/1.91         (~ (r2_hidden @ X7 @ X6)
% 1.69/1.91          | (r2_hidden @ X7 @ X5)
% 1.69/1.91          | ((X6) != (k3_xboole_0 @ X4 @ X5)))),
% 1.69/1.91      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.69/1.91  thf('22', plain,
% 1.69/1.91      (![X4 : $i, X5 : $i, X7 : $i]:
% 1.69/1.91         ((r2_hidden @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.69/1.91      inference('simplify', [status(thm)], ['21'])).
% 1.69/1.91  thf('23', plain,
% 1.69/1.91      (![X0 : $i]:
% 1.69/1.91         (~ (r2_hidden @ X0 @ sk_B_1) | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.69/1.91      inference('sup-', [status(thm)], ['20', '22'])).
% 1.69/1.91  thf('24', plain,
% 1.69/1.91      (((v1_xboole_0 @ sk_B_1)
% 1.69/1.91        | (r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 1.69/1.91      inference('sup-', [status(thm)], ['11', '23'])).
% 1.69/1.91  thf('25', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('26', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.69/1.91      inference('clc', [status(thm)], ['24', '25'])).
% 1.69/1.91  thf('27', plain,
% 1.69/1.91      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.69/1.91      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.69/1.91  thf('28', plain,
% 1.69/1.91      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.69/1.91         (~ (r2_hidden @ X3 @ X4)
% 1.69/1.91          | ~ (r2_hidden @ X3 @ X5)
% 1.69/1.91          | (r2_hidden @ X3 @ X6)
% 1.69/1.91          | ((X6) != (k3_xboole_0 @ X4 @ X5)))),
% 1.69/1.91      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.69/1.91  thf('29', plain,
% 1.69/1.91      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.69/1.91         ((r2_hidden @ X3 @ (k3_xboole_0 @ X4 @ X5))
% 1.69/1.91          | ~ (r2_hidden @ X3 @ X5)
% 1.69/1.91          | ~ (r2_hidden @ X3 @ X4))),
% 1.69/1.91      inference('simplify', [status(thm)], ['28'])).
% 1.69/1.91  thf('30', plain,
% 1.69/1.91      (![X0 : $i, X1 : $i]:
% 1.69/1.91         ((v1_xboole_0 @ X0)
% 1.69/1.91          | ~ (r2_hidden @ (sk_B @ X0) @ X1)
% 1.69/1.91          | (r2_hidden @ (sk_B @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.69/1.91      inference('sup-', [status(thm)], ['27', '29'])).
% 1.69/1.91  thf('31', plain,
% 1.69/1.91      (((r2_hidden @ (sk_B @ sk_B_1) @ 
% 1.69/1.91         (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 1.69/1.91        | (v1_xboole_0 @ sk_B_1))),
% 1.69/1.91      inference('sup-', [status(thm)], ['26', '30'])).
% 1.69/1.91  thf('32', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('33', plain,
% 1.69/1.91      ((r2_hidden @ (sk_B @ sk_B_1) @ 
% 1.69/1.91        (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 1.69/1.91      inference('clc', [status(thm)], ['31', '32'])).
% 1.69/1.91  thf('34', plain,
% 1.69/1.91      (![X4 : $i, X5 : $i, X7 : $i]:
% 1.69/1.91         ((r2_hidden @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k3_xboole_0 @ X4 @ X5)))),
% 1.69/1.91      inference('simplify', [status(thm)], ['21'])).
% 1.69/1.91  thf('35', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)),
% 1.69/1.91      inference('sup-', [status(thm)], ['33', '34'])).
% 1.69/1.91  thf(t63_subset_1, axiom,
% 1.69/1.91    (![A:$i,B:$i]:
% 1.69/1.91     ( ( r2_hidden @ A @ B ) =>
% 1.69/1.91       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.69/1.91  thf('36', plain,
% 1.69/1.91      (![X17 : $i, X18 : $i]:
% 1.69/1.91         ((m1_subset_1 @ (k1_tarski @ X17) @ (k1_zfmisc_1 @ X18))
% 1.69/1.91          | ~ (r2_hidden @ X17 @ X18))),
% 1.69/1.91      inference('cnf', [status(esa)], [t63_subset_1])).
% 1.69/1.91  thf('37', plain,
% 1.69/1.91      ((m1_subset_1 @ (k1_tarski @ (sk_B @ sk_B_1)) @ (k1_zfmisc_1 @ sk_B_1))),
% 1.69/1.91      inference('sup-', [status(thm)], ['35', '36'])).
% 1.69/1.91  thf('38', plain,
% 1.69/1.91      (![X23 : $i, X24 : $i]:
% 1.69/1.91         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 1.69/1.91      inference('cnf', [status(esa)], [t3_subset])).
% 1.69/1.91  thf('39', plain, ((r1_tarski @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_B_1)),
% 1.69/1.91      inference('sup-', [status(thm)], ['37', '38'])).
% 1.69/1.91  thf(t1_tex_2, axiom,
% 1.69/1.91    (![A:$i]:
% 1.69/1.91     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.69/1.91       ( ![B:$i]:
% 1.69/1.91         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 1.69/1.91           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 1.69/1.91  thf('40', plain,
% 1.69/1.91      (![X35 : $i, X36 : $i]:
% 1.69/1.91         ((v1_xboole_0 @ X35)
% 1.69/1.91          | ~ (v1_zfmisc_1 @ X35)
% 1.69/1.91          | ((X36) = (X35))
% 1.69/1.91          | ~ (r1_tarski @ X36 @ X35)
% 1.69/1.91          | (v1_xboole_0 @ X36))),
% 1.69/1.91      inference('cnf', [status(esa)], [t1_tex_2])).
% 1.69/1.91  thf('41', plain,
% 1.69/1.91      (((v1_xboole_0 @ (k1_tarski @ (sk_B @ sk_B_1)))
% 1.69/1.91        | ((k1_tarski @ (sk_B @ sk_B_1)) = (sk_B_1))
% 1.69/1.91        | ~ (v1_zfmisc_1 @ sk_B_1)
% 1.69/1.91        | (v1_xboole_0 @ sk_B_1))),
% 1.69/1.91      inference('sup-', [status(thm)], ['39', '40'])).
% 1.69/1.91  thf('42', plain,
% 1.69/1.91      ((((v1_xboole_0 @ sk_B_1)
% 1.69/1.91         | ((k1_tarski @ (sk_B @ sk_B_1)) = (sk_B_1))
% 1.69/1.91         | (v1_xboole_0 @ (k1_tarski @ (sk_B @ sk_B_1)))))
% 1.69/1.91         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.69/1.91      inference('sup-', [status(thm)], ['10', '41'])).
% 1.69/1.91  thf('43', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('44', plain,
% 1.69/1.91      ((((v1_xboole_0 @ (k1_tarski @ (sk_B @ sk_B_1)))
% 1.69/1.91         | ((k1_tarski @ (sk_B @ sk_B_1)) = (sk_B_1))))
% 1.69/1.91         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.69/1.91      inference('clc', [status(thm)], ['42', '43'])).
% 1.69/1.91  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 1.69/1.91  thf('45', plain, (![X16 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X16))),
% 1.69/1.91      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 1.69/1.91  thf('46', plain,
% 1.69/1.91      ((((k1_tarski @ (sk_B @ sk_B_1)) = (sk_B_1)))
% 1.69/1.91         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.69/1.91      inference('clc', [status(thm)], ['44', '45'])).
% 1.69/1.91  thf('47', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.69/1.91      inference('clc', [status(thm)], ['24', '25'])).
% 1.69/1.91  thf(t1_subset, axiom,
% 1.69/1.91    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.69/1.91  thf('48', plain,
% 1.69/1.91      (![X21 : $i, X22 : $i]:
% 1.69/1.91         ((m1_subset_1 @ X21 @ X22) | ~ (r2_hidden @ X21 @ X22))),
% 1.69/1.91      inference('cnf', [status(esa)], [t1_subset])).
% 1.69/1.91  thf('49', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.69/1.91      inference('sup-', [status(thm)], ['47', '48'])).
% 1.69/1.91  thf(t36_tex_2, axiom,
% 1.69/1.91    (![A:$i]:
% 1.69/1.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.69/1.91       ( ![B:$i]:
% 1.69/1.91         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.69/1.91           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 1.69/1.91  thf('50', plain,
% 1.69/1.91      (![X39 : $i, X40 : $i]:
% 1.69/1.91         (~ (m1_subset_1 @ X39 @ (u1_struct_0 @ X40))
% 1.69/1.91          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X40) @ X39) @ X40)
% 1.69/1.91          | ~ (l1_pre_topc @ X40)
% 1.69/1.91          | ~ (v2_pre_topc @ X40)
% 1.69/1.91          | (v2_struct_0 @ X40))),
% 1.69/1.91      inference('cnf', [status(esa)], [t36_tex_2])).
% 1.69/1.91  thf('51', plain,
% 1.69/1.91      (((v2_struct_0 @ sk_A)
% 1.69/1.91        | ~ (v2_pre_topc @ sk_A)
% 1.69/1.91        | ~ (l1_pre_topc @ sk_A)
% 1.69/1.91        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 1.69/1.91           sk_A))),
% 1.69/1.91      inference('sup-', [status(thm)], ['49', '50'])).
% 1.69/1.91  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('54', plain,
% 1.69/1.91      (((v2_struct_0 @ sk_A)
% 1.69/1.91        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 1.69/1.91           sk_A))),
% 1.69/1.91      inference('demod', [status(thm)], ['51', '52', '53'])).
% 1.69/1.91  thf('55', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 1.69/1.91      inference('sup-', [status(thm)], ['47', '48'])).
% 1.69/1.91  thf(redefinition_k6_domain_1, axiom,
% 1.69/1.91    (![A:$i,B:$i]:
% 1.69/1.91     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 1.69/1.91       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 1.69/1.91  thf('56', plain,
% 1.69/1.91      (![X30 : $i, X31 : $i]:
% 1.69/1.91         ((v1_xboole_0 @ X30)
% 1.69/1.91          | ~ (m1_subset_1 @ X31 @ X30)
% 1.69/1.91          | ((k6_domain_1 @ X30 @ X31) = (k1_tarski @ X31)))),
% 1.69/1.91      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 1.69/1.91  thf('57', plain,
% 1.69/1.91      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 1.69/1.91          = (k1_tarski @ (sk_B @ sk_B_1)))
% 1.69/1.91        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.69/1.91      inference('sup-', [status(thm)], ['55', '56'])).
% 1.69/1.91  thf('58', plain,
% 1.69/1.91      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf(cc1_subset_1, axiom,
% 1.69/1.91    (![A:$i]:
% 1.69/1.91     ( ( v1_xboole_0 @ A ) =>
% 1.69/1.91       ( ![B:$i]:
% 1.69/1.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 1.69/1.91  thf('59', plain,
% 1.69/1.91      (![X19 : $i, X20 : $i]:
% 1.69/1.91         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 1.69/1.91          | (v1_xboole_0 @ X19)
% 1.69/1.91          | ~ (v1_xboole_0 @ X20))),
% 1.69/1.91      inference('cnf', [status(esa)], [cc1_subset_1])).
% 1.69/1.91  thf('60', plain,
% 1.69/1.91      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 1.69/1.91      inference('sup-', [status(thm)], ['58', '59'])).
% 1.69/1.91  thf('61', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('62', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 1.69/1.91      inference('clc', [status(thm)], ['60', '61'])).
% 1.69/1.91  thf('63', plain,
% 1.69/1.91      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 1.69/1.91         = (k1_tarski @ (sk_B @ sk_B_1)))),
% 1.69/1.91      inference('clc', [status(thm)], ['57', '62'])).
% 1.69/1.91  thf('64', plain,
% 1.69/1.91      (((v2_struct_0 @ sk_A)
% 1.69/1.91        | (v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A))),
% 1.69/1.91      inference('demod', [status(thm)], ['54', '63'])).
% 1.69/1.91  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('66', plain, ((v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)),
% 1.69/1.91      inference('clc', [status(thm)], ['64', '65'])).
% 1.69/1.91  thf('67', plain,
% 1.69/1.91      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 1.69/1.91      inference('sup+', [status(thm)], ['46', '66'])).
% 1.69/1.91  thf('68', plain,
% 1.69/1.91      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.69/1.91      inference('split', [status(esa)], ['8'])).
% 1.69/1.91  thf('69', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ~ ((v1_zfmisc_1 @ sk_B_1))),
% 1.69/1.91      inference('sup-', [status(thm)], ['67', '68'])).
% 1.69/1.91  thf('70', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ((v1_zfmisc_1 @ sk_B_1))),
% 1.69/1.91      inference('split', [status(esa)], ['6'])).
% 1.69/1.91  thf('71', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.69/1.91      inference('sat_resolution*', [status(thm)], ['9', '69', '70'])).
% 1.69/1.91  thf('72', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 1.69/1.91      inference('simpl_trail', [status(thm)], ['7', '71'])).
% 1.69/1.91  thf('73', plain,
% 1.69/1.91      (((v2_struct_0 @ sk_A)
% 1.69/1.91        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 1.69/1.91        | (v1_xboole_0 @ sk_B_1))),
% 1.69/1.91      inference('demod', [status(thm)], ['5', '72'])).
% 1.69/1.91  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('75', plain,
% 1.69/1.91      (((v1_xboole_0 @ sk_B_1) | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 1.69/1.91      inference('clc', [status(thm)], ['73', '74'])).
% 1.69/1.91  thf('76', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('77', plain, (~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 1.69/1.91      inference('clc', [status(thm)], ['75', '76'])).
% 1.69/1.91  thf('78', plain,
% 1.69/1.91      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('79', plain,
% 1.69/1.91      (![X37 : $i, X38 : $i]:
% 1.69/1.91         ((v1_xboole_0 @ X37)
% 1.69/1.91          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 1.69/1.91          | ~ (v2_tex_2 @ X37 @ X38)
% 1.69/1.91          | (m1_pre_topc @ (sk_C @ X37 @ X38) @ X38)
% 1.69/1.91          | ~ (l1_pre_topc @ X38)
% 1.69/1.91          | ~ (v2_pre_topc @ X38)
% 1.69/1.91          | (v2_struct_0 @ X38))),
% 1.69/1.91      inference('cnf', [status(esa)], [t34_tex_2])).
% 1.69/1.91  thf('80', plain,
% 1.69/1.91      (((v2_struct_0 @ sk_A)
% 1.69/1.91        | ~ (v2_pre_topc @ sk_A)
% 1.69/1.91        | ~ (l1_pre_topc @ sk_A)
% 1.69/1.91        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 1.69/1.91        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 1.69/1.91        | (v1_xboole_0 @ sk_B_1))),
% 1.69/1.91      inference('sup-', [status(thm)], ['78', '79'])).
% 1.69/1.91  thf('81', plain, ((v2_pre_topc @ sk_A)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('83', plain,
% 1.69/1.91      (((v2_struct_0 @ sk_A)
% 1.69/1.91        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 1.69/1.91        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 1.69/1.91        | (v1_xboole_0 @ sk_B_1))),
% 1.69/1.91      inference('demod', [status(thm)], ['80', '81', '82'])).
% 1.69/1.91  thf('84', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 1.69/1.91      inference('simpl_trail', [status(thm)], ['7', '71'])).
% 1.69/1.91  thf('85', plain,
% 1.69/1.91      (((v2_struct_0 @ sk_A)
% 1.69/1.91        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 1.69/1.91        | (v1_xboole_0 @ sk_B_1))),
% 1.69/1.91      inference('demod', [status(thm)], ['83', '84'])).
% 1.69/1.91  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('87', plain,
% 1.69/1.91      (((v1_xboole_0 @ sk_B_1) | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))),
% 1.69/1.91      inference('clc', [status(thm)], ['85', '86'])).
% 1.69/1.91  thf('88', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('89', plain, ((m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 1.69/1.91      inference('clc', [status(thm)], ['87', '88'])).
% 1.69/1.91  thf(cc32_tex_2, axiom,
% 1.69/1.91    (![A:$i]:
% 1.69/1.91     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 1.69/1.91         ( l1_pre_topc @ A ) ) =>
% 1.69/1.91       ( ![B:$i]:
% 1.69/1.91         ( ( m1_pre_topc @ B @ A ) =>
% 1.69/1.91           ( ( ( ~( v2_struct_0 @ B ) ) & ( ~( v7_struct_0 @ B ) ) ) =>
% 1.69/1.91             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tdlat_3 @ B ) ) ) ) ) ) ))).
% 1.69/1.91  thf('90', plain,
% 1.69/1.91      (![X33 : $i, X34 : $i]:
% 1.69/1.91         (~ (m1_pre_topc @ X33 @ X34)
% 1.69/1.91          | ~ (v1_tdlat_3 @ X33)
% 1.69/1.91          | (v7_struct_0 @ X33)
% 1.69/1.91          | (v2_struct_0 @ X33)
% 1.69/1.91          | ~ (l1_pre_topc @ X34)
% 1.69/1.91          | ~ (v2_tdlat_3 @ X34)
% 1.69/1.91          | ~ (v2_pre_topc @ X34)
% 1.69/1.91          | (v2_struct_0 @ X34))),
% 1.69/1.91      inference('cnf', [status(esa)], [cc32_tex_2])).
% 1.69/1.91  thf('91', plain,
% 1.69/1.91      (((v2_struct_0 @ sk_A)
% 1.69/1.91        | ~ (v2_pre_topc @ sk_A)
% 1.69/1.91        | ~ (v2_tdlat_3 @ sk_A)
% 1.69/1.91        | ~ (l1_pre_topc @ sk_A)
% 1.69/1.91        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 1.69/1.91        | (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 1.69/1.91        | ~ (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A)))),
% 1.69/1.91      inference('sup-', [status(thm)], ['89', '90'])).
% 1.69/1.91  thf('92', plain, ((v2_pre_topc @ sk_A)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('93', plain, ((v2_tdlat_3 @ sk_A)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('95', plain,
% 1.69/1.91      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.69/1.91      inference('split', [status(esa)], ['6'])).
% 1.69/1.91  thf('96', plain,
% 1.69/1.91      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('97', plain,
% 1.69/1.91      (![X37 : $i, X38 : $i]:
% 1.69/1.91         ((v1_xboole_0 @ X37)
% 1.69/1.91          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 1.69/1.91          | ~ (v2_tex_2 @ X37 @ X38)
% 1.69/1.91          | (v1_tdlat_3 @ (sk_C @ X37 @ X38))
% 1.69/1.91          | ~ (l1_pre_topc @ X38)
% 1.69/1.91          | ~ (v2_pre_topc @ X38)
% 1.69/1.91          | (v2_struct_0 @ X38))),
% 1.69/1.91      inference('cnf', [status(esa)], [t34_tex_2])).
% 1.69/1.91  thf('98', plain,
% 1.69/1.91      (((v2_struct_0 @ sk_A)
% 1.69/1.91        | ~ (v2_pre_topc @ sk_A)
% 1.69/1.91        | ~ (l1_pre_topc @ sk_A)
% 1.69/1.91        | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 1.69/1.91        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 1.69/1.91        | (v1_xboole_0 @ sk_B_1))),
% 1.69/1.91      inference('sup-', [status(thm)], ['96', '97'])).
% 1.69/1.91  thf('99', plain, ((v2_pre_topc @ sk_A)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('101', plain,
% 1.69/1.91      (((v2_struct_0 @ sk_A)
% 1.69/1.91        | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 1.69/1.91        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 1.69/1.91        | (v1_xboole_0 @ sk_B_1))),
% 1.69/1.91      inference('demod', [status(thm)], ['98', '99', '100'])).
% 1.69/1.91  thf('102', plain,
% 1.69/1.91      ((((v1_xboole_0 @ sk_B_1)
% 1.69/1.91         | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 1.69/1.91         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.69/1.91      inference('sup-', [status(thm)], ['95', '101'])).
% 1.69/1.91  thf('103', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('104', plain,
% 1.69/1.91      ((((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))))
% 1.69/1.91         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.69/1.91      inference('clc', [status(thm)], ['102', '103'])).
% 1.69/1.91  thf('105', plain, (~ (v2_struct_0 @ sk_A)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('106', plain,
% 1.69/1.91      (((v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A)))
% 1.69/1.91         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.69/1.91      inference('clc', [status(thm)], ['104', '105'])).
% 1.69/1.91  thf('107', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.69/1.91      inference('sat_resolution*', [status(thm)], ['9', '69', '70'])).
% 1.69/1.91  thf('108', plain, ((v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))),
% 1.69/1.91      inference('simpl_trail', [status(thm)], ['106', '107'])).
% 1.69/1.91  thf('109', plain,
% 1.69/1.91      (((v2_struct_0 @ sk_A)
% 1.69/1.91        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 1.69/1.91        | (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 1.69/1.91      inference('demod', [status(thm)], ['91', '92', '93', '94', '108'])).
% 1.69/1.91  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('111', plain,
% 1.69/1.91      (((v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 1.69/1.91        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 1.69/1.91      inference('clc', [status(thm)], ['109', '110'])).
% 1.69/1.91  thf('112', plain,
% 1.69/1.91      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.69/1.91      inference('split', [status(esa)], ['6'])).
% 1.69/1.91  thf('113', plain,
% 1.69/1.91      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('114', plain,
% 1.69/1.91      (![X37 : $i, X38 : $i]:
% 1.69/1.91         ((v1_xboole_0 @ X37)
% 1.69/1.91          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 1.69/1.91          | ~ (v2_tex_2 @ X37 @ X38)
% 1.69/1.91          | ((X37) = (u1_struct_0 @ (sk_C @ X37 @ X38)))
% 1.69/1.91          | ~ (l1_pre_topc @ X38)
% 1.69/1.91          | ~ (v2_pre_topc @ X38)
% 1.69/1.91          | (v2_struct_0 @ X38))),
% 1.69/1.91      inference('cnf', [status(esa)], [t34_tex_2])).
% 1.69/1.91  thf('115', plain,
% 1.69/1.91      (((v2_struct_0 @ sk_A)
% 1.69/1.91        | ~ (v2_pre_topc @ sk_A)
% 1.69/1.91        | ~ (l1_pre_topc @ sk_A)
% 1.69/1.91        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 1.69/1.91        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 1.69/1.91        | (v1_xboole_0 @ sk_B_1))),
% 1.69/1.91      inference('sup-', [status(thm)], ['113', '114'])).
% 1.69/1.91  thf('116', plain, ((v2_pre_topc @ sk_A)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('117', plain, ((l1_pre_topc @ sk_A)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('118', plain,
% 1.69/1.91      (((v2_struct_0 @ sk_A)
% 1.69/1.91        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 1.69/1.91        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 1.69/1.91        | (v1_xboole_0 @ sk_B_1))),
% 1.69/1.91      inference('demod', [status(thm)], ['115', '116', '117'])).
% 1.69/1.91  thf('119', plain,
% 1.69/1.91      ((((v1_xboole_0 @ sk_B_1)
% 1.69/1.91         | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 1.69/1.91         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.69/1.91      inference('sup-', [status(thm)], ['112', '118'])).
% 1.69/1.91  thf('120', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('121', plain,
% 1.69/1.91      ((((v2_struct_0 @ sk_A)
% 1.69/1.91         | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))))
% 1.69/1.91         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.69/1.91      inference('clc', [status(thm)], ['119', '120'])).
% 1.69/1.91  thf('122', plain, (~ (v2_struct_0 @ sk_A)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('123', plain,
% 1.69/1.91      ((((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 1.69/1.91         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.69/1.91      inference('clc', [status(thm)], ['121', '122'])).
% 1.69/1.91  thf(fc7_struct_0, axiom,
% 1.69/1.91    (![A:$i]:
% 1.69/1.91     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 1.69/1.91       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 1.69/1.91  thf('124', plain,
% 1.69/1.91      (![X29 : $i]:
% 1.69/1.91         ((v1_zfmisc_1 @ (u1_struct_0 @ X29))
% 1.69/1.91          | ~ (l1_struct_0 @ X29)
% 1.69/1.91          | ~ (v7_struct_0 @ X29))),
% 1.69/1.91      inference('cnf', [status(esa)], [fc7_struct_0])).
% 1.69/1.91  thf('125', plain,
% 1.69/1.91      ((((v1_zfmisc_1 @ sk_B_1)
% 1.69/1.91         | ~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 1.69/1.91         | ~ (l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))
% 1.69/1.91         <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 1.69/1.91      inference('sup+', [status(thm)], ['123', '124'])).
% 1.69/1.91  thf('126', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 1.69/1.91      inference('sat_resolution*', [status(thm)], ['9', '69', '70'])).
% 1.69/1.91  thf('127', plain,
% 1.69/1.91      (((v1_zfmisc_1 @ sk_B_1)
% 1.69/1.91        | ~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 1.69/1.91        | ~ (l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 1.69/1.91      inference('simpl_trail', [status(thm)], ['125', '126'])).
% 1.69/1.91  thf('128', plain,
% 1.69/1.91      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 1.69/1.91      inference('split', [status(esa)], ['8'])).
% 1.69/1.91  thf('129', plain, (~ ((v1_zfmisc_1 @ sk_B_1))),
% 1.69/1.91      inference('sat_resolution*', [status(thm)], ['9', '69'])).
% 1.69/1.91  thf('130', plain, (~ (v1_zfmisc_1 @ sk_B_1)),
% 1.69/1.91      inference('simpl_trail', [status(thm)], ['128', '129'])).
% 1.69/1.91  thf('131', plain,
% 1.69/1.91      ((~ (l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 1.69/1.91        | ~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 1.69/1.91      inference('clc', [status(thm)], ['127', '130'])).
% 1.69/1.91  thf('132', plain, ((m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 1.69/1.91      inference('clc', [status(thm)], ['87', '88'])).
% 1.69/1.91  thf(dt_m1_pre_topc, axiom,
% 1.69/1.91    (![A:$i]:
% 1.69/1.91     ( ( l1_pre_topc @ A ) =>
% 1.69/1.91       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.69/1.91  thf('133', plain,
% 1.69/1.91      (![X27 : $i, X28 : $i]:
% 1.69/1.91         (~ (m1_pre_topc @ X27 @ X28)
% 1.69/1.91          | (l1_pre_topc @ X27)
% 1.69/1.91          | ~ (l1_pre_topc @ X28))),
% 1.69/1.91      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.69/1.91  thf('134', plain,
% 1.69/1.91      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A)))),
% 1.69/1.91      inference('sup-', [status(thm)], ['132', '133'])).
% 1.69/1.91  thf('135', plain, ((l1_pre_topc @ sk_A)),
% 1.69/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.69/1.91  thf('136', plain, ((l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A))),
% 1.69/1.91      inference('demod', [status(thm)], ['134', '135'])).
% 1.69/1.91  thf(dt_l1_pre_topc, axiom,
% 1.69/1.91    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.69/1.91  thf('137', plain,
% 1.69/1.91      (![X26 : $i]: ((l1_struct_0 @ X26) | ~ (l1_pre_topc @ X26))),
% 1.69/1.91      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.69/1.91  thf('138', plain, ((l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 1.69/1.91      inference('sup-', [status(thm)], ['136', '137'])).
% 1.69/1.91  thf('139', plain, (~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 1.69/1.91      inference('demod', [status(thm)], ['131', '138'])).
% 1.69/1.91  thf('140', plain, ((v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 1.69/1.91      inference('clc', [status(thm)], ['111', '139'])).
% 1.69/1.91  thf('141', plain, ($false), inference('demod', [status(thm)], ['77', '140'])).
% 1.69/1.91  
% 1.69/1.91  % SZS output end Refutation
% 1.69/1.91  
% 1.69/1.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
