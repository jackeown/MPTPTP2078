%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hgxiT87uix

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:58 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  173 (1076 expanded)
%              Number of leaves         :   41 ( 320 expanded)
%              Depth                    :   26
%              Number of atoms          : 1072 (10951 expanded)
%              Number of equality atoms :   28 ( 215 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ! [X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v2_tex_2 @ X33 @ X34 )
      | ~ ( v2_struct_0 @ ( sk_C @ X33 @ X34 ) )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
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

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('12',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X12 ) @ X14 )
      | ~ ( r2_hidden @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('14',plain,(
    ! [X31: $i,X32: $i] :
      ( ( v1_xboole_0 @ X31 )
      | ~ ( v1_zfmisc_1 @ X31 )
      | ( X32 = X31 )
      | ~ ( r1_tarski @ X32 @ X31 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X11: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('24',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X5 )
      | ( X6
       != ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('26',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','27'])).

thf('29',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X12 ) @ X14 )
      | ~ ( r2_hidden @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('32',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k3_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('34',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['18','34'])).

thf('36',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('37',plain,
    ( ( sk_B_1
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B_1
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','39'])).

thf('41',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['28','29'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ X17 @ X18 )
      | ~ ( r2_hidden @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('43',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('44',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X36 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X36 ) @ X35 ) @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('49',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ X26 )
      | ( ( k6_domain_1 @ X26 @ X27 )
        = ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('50',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('52',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( v1_xboole_0 @ X15 )
      | ~ ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('53',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['50','55'])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['45','46','47','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['40','59'])).

thf('61',plain,
    ( ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('62',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('64',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['9','62','63'])).

thf('65',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','64'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['5','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v2_tex_2 @ X33 @ X34 )
      | ( m1_pre_topc @ ( sk_C @ X33 @ X34 ) @ X34 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','64'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['80','81'])).

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

thf('83',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( v1_tdlat_3 @ X29 )
      | ( v7_struct_0 @ X29 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_tdlat_3 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[cc32_tex_2])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v2_tex_2 @ X33 @ X34 )
      | ( v1_tdlat_3 @ ( sk_C @ X33 @ X34 ) )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','64'])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_tdlat_3 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85','86','87','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v2_tex_2 @ X33 @ X34 )
      | ( X33
        = ( u1_struct_0 @ ( sk_C @ X33 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['7','64'])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( sk_B_1
    = ( u1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['112','113'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('115',plain,(
    ! [X25: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ~ ( v7_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('116',plain,
    ( ( v1_zfmisc_1 @ sk_B_1 )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
   <= ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('118',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['9','62'])).

thf('119',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['117','118'])).

thf('120',plain,
    ( ~ ( l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) )
    | ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['116','119'])).

thf('121',plain,(
    m1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['80','81'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('122',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( l1_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('123',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    l1_pre_topc @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['123','124'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('126',plain,(
    ! [X22: $i] :
      ( ( l1_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('127',plain,(
    l1_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( v7_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['120','127'])).

thf('129',plain,(
    v2_struct_0 @ ( sk_C @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['102','128'])).

thf('130',plain,(
    $false ),
    inference(demod,[status(thm)],['70','129'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hgxiT87uix
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:52:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.76  % Solved by: fo/fo7.sh
% 0.58/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.76  % done 405 iterations in 0.310s
% 0.58/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.76  % SZS output start Refutation
% 0.58/0.76  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.58/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.76  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.58/0.76  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.58/0.76  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.58/0.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.76  thf(sk_B_type, type, sk_B: $i > $i).
% 0.58/0.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.76  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.58/0.76  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.76  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.76  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.58/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.76  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.58/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.76  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.58/0.76  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.58/0.76  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.58/0.76  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.58/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.76  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.58/0.76  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.58/0.76  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.58/0.76  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.58/0.76  thf(t44_tex_2, conjecture,
% 0.58/0.76    (![A:$i]:
% 0.58/0.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.58/0.76         ( l1_pre_topc @ A ) ) =>
% 0.58/0.76       ( ![B:$i]:
% 0.58/0.76         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.58/0.76             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.58/0.76           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.58/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.76    (~( ![A:$i]:
% 0.58/0.76        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.58/0.76            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.76          ( ![B:$i]:
% 0.58/0.76            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.58/0.76                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.58/0.76              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.58/0.76    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.58/0.76  thf('0', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(t34_tex_2, axiom,
% 0.58/0.76    (![A:$i]:
% 0.58/0.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.76       ( ![B:$i]:
% 0.58/0.76         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.58/0.76             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.58/0.76           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.58/0.76                ( ![C:$i]:
% 0.58/0.76                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.58/0.76                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.58/0.76                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 0.58/0.76  thf('1', plain,
% 0.58/0.76      (![X33 : $i, X34 : $i]:
% 0.58/0.76         ((v1_xboole_0 @ X33)
% 0.58/0.76          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.58/0.76          | ~ (v2_tex_2 @ X33 @ X34)
% 0.58/0.76          | ~ (v2_struct_0 @ (sk_C @ X33 @ X34))
% 0.58/0.76          | ~ (l1_pre_topc @ X34)
% 0.58/0.76          | ~ (v2_pre_topc @ X34)
% 0.58/0.76          | (v2_struct_0 @ X34))),
% 0.58/0.76      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.58/0.76  thf('2', plain,
% 0.58/0.76      (((v2_struct_0 @ sk_A)
% 0.58/0.76        | ~ (v2_pre_topc @ sk_A)
% 0.58/0.76        | ~ (l1_pre_topc @ sk_A)
% 0.58/0.76        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.58/0.76        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.58/0.76        | (v1_xboole_0 @ sk_B_1))),
% 0.58/0.76      inference('sup-', [status(thm)], ['0', '1'])).
% 0.58/0.76  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('5', plain,
% 0.58/0.76      (((v2_struct_0 @ sk_A)
% 0.58/0.76        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.58/0.76        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.58/0.76        | (v1_xboole_0 @ sk_B_1))),
% 0.58/0.76      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.58/0.76  thf('6', plain, (((v1_zfmisc_1 @ sk_B_1) | (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('7', plain,
% 0.58/0.76      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.58/0.76      inference('split', [status(esa)], ['6'])).
% 0.58/0.76  thf('8', plain, ((~ (v1_zfmisc_1 @ sk_B_1) | ~ (v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('9', plain,
% 0.58/0.76      (~ ((v1_zfmisc_1 @ sk_B_1)) | ~ ((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.58/0.76      inference('split', [status(esa)], ['8'])).
% 0.58/0.76  thf('10', plain, (((v1_zfmisc_1 @ sk_B_1)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.58/0.76      inference('split', [status(esa)], ['6'])).
% 0.58/0.76  thf(d1_xboole_0, axiom,
% 0.58/0.76    (![A:$i]:
% 0.58/0.76     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.58/0.76  thf('11', plain,
% 0.58/0.76      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.58/0.76      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.58/0.76  thf(l1_zfmisc_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.58/0.76  thf('12', plain,
% 0.58/0.76      (![X12 : $i, X14 : $i]:
% 0.58/0.76         ((r1_tarski @ (k1_tarski @ X12) @ X14) | ~ (r2_hidden @ X12 @ X14))),
% 0.58/0.76      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.58/0.76  thf('13', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['11', '12'])).
% 0.58/0.76  thf(t1_tex_2, axiom,
% 0.58/0.76    (![A:$i]:
% 0.58/0.76     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.58/0.76       ( ![B:$i]:
% 0.58/0.76         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.58/0.76           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.58/0.76  thf('14', plain,
% 0.58/0.76      (![X31 : $i, X32 : $i]:
% 0.58/0.76         ((v1_xboole_0 @ X31)
% 0.58/0.76          | ~ (v1_zfmisc_1 @ X31)
% 0.58/0.76          | ((X32) = (X31))
% 0.58/0.76          | ~ (r1_tarski @ X32 @ X31)
% 0.58/0.76          | (v1_xboole_0 @ X32))),
% 0.58/0.76      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.58/0.76  thf('15', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         ((v1_xboole_0 @ X0)
% 0.58/0.76          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.58/0.76          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.58/0.76          | ~ (v1_zfmisc_1 @ X0)
% 0.58/0.76          | (v1_xboole_0 @ X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['13', '14'])).
% 0.58/0.76  thf('16', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (~ (v1_zfmisc_1 @ X0)
% 0.58/0.76          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.58/0.76          | (v1_xboole_0 @ (k1_tarski @ (sk_B @ X0)))
% 0.58/0.76          | (v1_xboole_0 @ X0))),
% 0.58/0.76      inference('simplify', [status(thm)], ['15'])).
% 0.58/0.76  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.58/0.76  thf('17', plain, (![X11 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X11))),
% 0.58/0.76      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.58/0.76  thf('18', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         ((v1_xboole_0 @ X0)
% 0.58/0.76          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.58/0.76          | ~ (v1_zfmisc_1 @ X0))),
% 0.58/0.76      inference('sup-', [status(thm)], ['16', '17'])).
% 0.58/0.76  thf('19', plain,
% 0.58/0.76      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.58/0.76      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.58/0.76  thf('20', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(t3_subset, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.58/0.76  thf('21', plain,
% 0.58/0.76      (![X19 : $i, X20 : $i]:
% 0.58/0.76         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.58/0.76      inference('cnf', [status(esa)], [t3_subset])).
% 0.58/0.76  thf('22', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.58/0.76      inference('sup-', [status(thm)], ['20', '21'])).
% 0.58/0.76  thf(t28_xboole_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.58/0.76  thf('23', plain,
% 0.58/0.76      (![X9 : $i, X10 : $i]:
% 0.58/0.76         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.58/0.76      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.58/0.76  thf('24', plain,
% 0.58/0.76      (((k3_xboole_0 @ sk_B_1 @ (u1_struct_0 @ sk_A)) = (sk_B_1))),
% 0.58/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.58/0.76  thf(d4_xboole_0, axiom,
% 0.58/0.76    (![A:$i,B:$i,C:$i]:
% 0.58/0.76     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.58/0.76       ( ![D:$i]:
% 0.58/0.76         ( ( r2_hidden @ D @ C ) <=>
% 0.58/0.76           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.58/0.76  thf('25', plain,
% 0.58/0.76      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X7 @ X6)
% 0.58/0.76          | (r2_hidden @ X7 @ X5)
% 0.58/0.76          | ((X6) != (k3_xboole_0 @ X4 @ X5)))),
% 0.58/0.76      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.58/0.76  thf('26', plain,
% 0.58/0.76      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.58/0.76         ((r2_hidden @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.58/0.76      inference('simplify', [status(thm)], ['25'])).
% 0.58/0.76  thf('27', plain,
% 0.58/0.76      (![X0 : $i]:
% 0.58/0.76         (~ (r2_hidden @ X0 @ sk_B_1) | (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['24', '26'])).
% 0.58/0.76  thf('28', plain,
% 0.58/0.76      (((v1_xboole_0 @ sk_B_1)
% 0.58/0.76        | (r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['19', '27'])).
% 0.58/0.76  thf('29', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('30', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.58/0.76      inference('clc', [status(thm)], ['28', '29'])).
% 0.58/0.76  thf('31', plain,
% 0.58/0.76      (![X12 : $i, X14 : $i]:
% 0.58/0.76         ((r1_tarski @ (k1_tarski @ X12) @ X14) | ~ (r2_hidden @ X12 @ X14))),
% 0.58/0.76      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.58/0.76  thf('32', plain,
% 0.58/0.76      ((r1_tarski @ (k1_tarski @ (sk_B @ sk_B_1)) @ (u1_struct_0 @ sk_A))),
% 0.58/0.76      inference('sup-', [status(thm)], ['30', '31'])).
% 0.58/0.76  thf('33', plain,
% 0.58/0.76      (![X9 : $i, X10 : $i]:
% 0.58/0.76         (((k3_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_tarski @ X9 @ X10))),
% 0.58/0.76      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.58/0.76  thf('34', plain,
% 0.58/0.76      (((k3_xboole_0 @ (k1_tarski @ (sk_B @ sk_B_1)) @ (u1_struct_0 @ sk_A))
% 0.58/0.76         = (k1_tarski @ (sk_B @ sk_B_1)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['32', '33'])).
% 0.58/0.76  thf('35', plain,
% 0.58/0.76      ((((k3_xboole_0 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.58/0.76          = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.58/0.76        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.58/0.76        | (v1_xboole_0 @ sk_B_1))),
% 0.58/0.76      inference('sup+', [status(thm)], ['18', '34'])).
% 0.58/0.76  thf('36', plain,
% 0.58/0.76      (((k3_xboole_0 @ sk_B_1 @ (u1_struct_0 @ sk_A)) = (sk_B_1))),
% 0.58/0.76      inference('sup-', [status(thm)], ['22', '23'])).
% 0.58/0.76  thf('37', plain,
% 0.58/0.76      ((((sk_B_1) = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.58/0.76        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.58/0.76        | (v1_xboole_0 @ sk_B_1))),
% 0.58/0.76      inference('demod', [status(thm)], ['35', '36'])).
% 0.58/0.76  thf('38', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('39', plain,
% 0.58/0.76      ((~ (v1_zfmisc_1 @ sk_B_1) | ((sk_B_1) = (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.58/0.76      inference('clc', [status(thm)], ['37', '38'])).
% 0.58/0.76  thf('40', plain,
% 0.58/0.76      ((((sk_B_1) = (k1_tarski @ (sk_B @ sk_B_1))))
% 0.58/0.76         <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['10', '39'])).
% 0.58/0.76  thf('41', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.58/0.76      inference('clc', [status(thm)], ['28', '29'])).
% 0.58/0.76  thf(t1_subset, axiom,
% 0.58/0.76    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.58/0.76  thf('42', plain,
% 0.58/0.76      (![X17 : $i, X18 : $i]:
% 0.58/0.76         ((m1_subset_1 @ X17 @ X18) | ~ (r2_hidden @ X17 @ X18))),
% 0.58/0.76      inference('cnf', [status(esa)], [t1_subset])).
% 0.58/0.76  thf('43', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.58/0.76      inference('sup-', [status(thm)], ['41', '42'])).
% 0.58/0.76  thf(t36_tex_2, axiom,
% 0.58/0.76    (![A:$i]:
% 0.58/0.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.58/0.76       ( ![B:$i]:
% 0.58/0.76         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.76           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.58/0.76  thf('44', plain,
% 0.58/0.76      (![X35 : $i, X36 : $i]:
% 0.58/0.76         (~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X36))
% 0.58/0.76          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X36) @ X35) @ X36)
% 0.58/0.76          | ~ (l1_pre_topc @ X36)
% 0.58/0.76          | ~ (v2_pre_topc @ X36)
% 0.58/0.76          | (v2_struct_0 @ X36))),
% 0.58/0.76      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.58/0.76  thf('45', plain,
% 0.58/0.76      (((v2_struct_0 @ sk_A)
% 0.58/0.76        | ~ (v2_pre_topc @ sk_A)
% 0.58/0.76        | ~ (l1_pre_topc @ sk_A)
% 0.58/0.76        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.58/0.76           sk_A))),
% 0.58/0.76      inference('sup-', [status(thm)], ['43', '44'])).
% 0.58/0.76  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('48', plain, ((m1_subset_1 @ (sk_B @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.58/0.76      inference('sup-', [status(thm)], ['41', '42'])).
% 0.58/0.76  thf(redefinition_k6_domain_1, axiom,
% 0.58/0.76    (![A:$i,B:$i]:
% 0.58/0.76     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.58/0.76       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.58/0.76  thf('49', plain,
% 0.58/0.76      (![X26 : $i, X27 : $i]:
% 0.58/0.76         ((v1_xboole_0 @ X26)
% 0.58/0.76          | ~ (m1_subset_1 @ X27 @ X26)
% 0.58/0.76          | ((k6_domain_1 @ X26 @ X27) = (k1_tarski @ X27)))),
% 0.58/0.76      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.58/0.76  thf('50', plain,
% 0.58/0.76      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.58/0.76          = (k1_tarski @ (sk_B @ sk_B_1)))
% 0.58/0.76        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['48', '49'])).
% 0.58/0.76  thf('51', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf(cc1_subset_1, axiom,
% 0.58/0.76    (![A:$i]:
% 0.58/0.76     ( ( v1_xboole_0 @ A ) =>
% 0.58/0.76       ( ![B:$i]:
% 0.58/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.58/0.76  thf('52', plain,
% 0.58/0.76      (![X15 : $i, X16 : $i]:
% 0.58/0.76         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.58/0.76          | (v1_xboole_0 @ X15)
% 0.58/0.76          | ~ (v1_xboole_0 @ X16))),
% 0.58/0.76      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.58/0.76  thf('53', plain,
% 0.58/0.76      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 0.58/0.76      inference('sup-', [status(thm)], ['51', '52'])).
% 0.58/0.76  thf('54', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('55', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.58/0.76      inference('clc', [status(thm)], ['53', '54'])).
% 0.58/0.76  thf('56', plain,
% 0.58/0.76      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1))
% 0.58/0.76         = (k1_tarski @ (sk_B @ sk_B_1)))),
% 0.58/0.76      inference('clc', [status(thm)], ['50', '55'])).
% 0.58/0.76  thf('57', plain,
% 0.58/0.76      (((v2_struct_0 @ sk_A)
% 0.58/0.76        | (v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A))),
% 0.58/0.76      inference('demod', [status(thm)], ['45', '46', '47', '56'])).
% 0.58/0.76  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('59', plain, ((v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_1)) @ sk_A)),
% 0.58/0.76      inference('clc', [status(thm)], ['57', '58'])).
% 0.58/0.76  thf('60', plain,
% 0.58/0.76      (((v2_tex_2 @ sk_B_1 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_1)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['40', '59'])).
% 0.58/0.76  thf('61', plain,
% 0.58/0.76      ((~ (v2_tex_2 @ sk_B_1 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_1 @ sk_A)))),
% 0.58/0.76      inference('split', [status(esa)], ['8'])).
% 0.58/0.76  thf('62', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.58/0.76      inference('sup-', [status(thm)], ['60', '61'])).
% 0.58/0.76  thf('63', plain, (((v2_tex_2 @ sk_B_1 @ sk_A)) | ((v1_zfmisc_1 @ sk_B_1))),
% 0.58/0.76      inference('split', [status(esa)], ['6'])).
% 0.58/0.76  thf('64', plain, (((v2_tex_2 @ sk_B_1 @ sk_A))),
% 0.58/0.76      inference('sat_resolution*', [status(thm)], ['9', '62', '63'])).
% 0.58/0.76  thf('65', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.58/0.76      inference('simpl_trail', [status(thm)], ['7', '64'])).
% 0.58/0.76  thf('66', plain,
% 0.58/0.76      (((v2_struct_0 @ sk_A)
% 0.58/0.76        | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.58/0.76        | (v1_xboole_0 @ sk_B_1))),
% 0.58/0.76      inference('demod', [status(thm)], ['5', '65'])).
% 0.58/0.76  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('68', plain,
% 0.58/0.76      (((v1_xboole_0 @ sk_B_1) | ~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.58/0.76      inference('clc', [status(thm)], ['66', '67'])).
% 0.58/0.76  thf('69', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('70', plain, (~ (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.58/0.76      inference('clc', [status(thm)], ['68', '69'])).
% 0.58/0.76  thf('71', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('72', plain,
% 0.58/0.76      (![X33 : $i, X34 : $i]:
% 0.58/0.76         ((v1_xboole_0 @ X33)
% 0.58/0.76          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.58/0.76          | ~ (v2_tex_2 @ X33 @ X34)
% 0.58/0.76          | (m1_pre_topc @ (sk_C @ X33 @ X34) @ X34)
% 0.58/0.76          | ~ (l1_pre_topc @ X34)
% 0.58/0.76          | ~ (v2_pre_topc @ X34)
% 0.58/0.76          | (v2_struct_0 @ X34))),
% 0.58/0.76      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.58/0.76  thf('73', plain,
% 0.58/0.76      (((v2_struct_0 @ sk_A)
% 0.58/0.76        | ~ (v2_pre_topc @ sk_A)
% 0.58/0.76        | ~ (l1_pre_topc @ sk_A)
% 0.58/0.76        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.58/0.76        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.58/0.76        | (v1_xboole_0 @ sk_B_1))),
% 0.58/0.76      inference('sup-', [status(thm)], ['71', '72'])).
% 0.58/0.76  thf('74', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('76', plain,
% 0.58/0.76      (((v2_struct_0 @ sk_A)
% 0.58/0.76        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.58/0.76        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.58/0.76        | (v1_xboole_0 @ sk_B_1))),
% 0.58/0.76      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.58/0.76  thf('77', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.58/0.76      inference('simpl_trail', [status(thm)], ['7', '64'])).
% 0.58/0.76  thf('78', plain,
% 0.58/0.76      (((v2_struct_0 @ sk_A)
% 0.58/0.76        | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.58/0.76        | (v1_xboole_0 @ sk_B_1))),
% 0.58/0.76      inference('demod', [status(thm)], ['76', '77'])).
% 0.58/0.76  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('80', plain,
% 0.58/0.76      (((v1_xboole_0 @ sk_B_1) | (m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))),
% 0.58/0.76      inference('clc', [status(thm)], ['78', '79'])).
% 0.58/0.76  thf('81', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('82', plain, ((m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 0.58/0.76      inference('clc', [status(thm)], ['80', '81'])).
% 0.58/0.76  thf(cc32_tex_2, axiom,
% 0.58/0.76    (![A:$i]:
% 0.58/0.76     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.58/0.76         ( l1_pre_topc @ A ) ) =>
% 0.58/0.76       ( ![B:$i]:
% 0.58/0.76         ( ( m1_pre_topc @ B @ A ) =>
% 0.58/0.76           ( ( ( ~( v2_struct_0 @ B ) ) & ( ~( v7_struct_0 @ B ) ) ) =>
% 0.58/0.76             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tdlat_3 @ B ) ) ) ) ) ) ))).
% 0.58/0.76  thf('83', plain,
% 0.58/0.76      (![X29 : $i, X30 : $i]:
% 0.58/0.76         (~ (m1_pre_topc @ X29 @ X30)
% 0.58/0.76          | ~ (v1_tdlat_3 @ X29)
% 0.58/0.76          | (v7_struct_0 @ X29)
% 0.58/0.76          | (v2_struct_0 @ X29)
% 0.58/0.76          | ~ (l1_pre_topc @ X30)
% 0.58/0.76          | ~ (v2_tdlat_3 @ X30)
% 0.58/0.76          | ~ (v2_pre_topc @ X30)
% 0.58/0.76          | (v2_struct_0 @ X30))),
% 0.58/0.76      inference('cnf', [status(esa)], [cc32_tex_2])).
% 0.58/0.76  thf('84', plain,
% 0.58/0.76      (((v2_struct_0 @ sk_A)
% 0.58/0.76        | ~ (v2_pre_topc @ sk_A)
% 0.58/0.76        | ~ (v2_tdlat_3 @ sk_A)
% 0.58/0.76        | ~ (l1_pre_topc @ sk_A)
% 0.58/0.76        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.58/0.76        | (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.58/0.76        | ~ (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['82', '83'])).
% 0.58/0.76  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('86', plain, ((v2_tdlat_3 @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('88', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('89', plain,
% 0.58/0.76      (![X33 : $i, X34 : $i]:
% 0.58/0.76         ((v1_xboole_0 @ X33)
% 0.58/0.76          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.58/0.76          | ~ (v2_tex_2 @ X33 @ X34)
% 0.58/0.76          | (v1_tdlat_3 @ (sk_C @ X33 @ X34))
% 0.58/0.76          | ~ (l1_pre_topc @ X34)
% 0.58/0.76          | ~ (v2_pre_topc @ X34)
% 0.58/0.76          | (v2_struct_0 @ X34))),
% 0.58/0.76      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.58/0.76  thf('90', plain,
% 0.58/0.76      (((v2_struct_0 @ sk_A)
% 0.58/0.76        | ~ (v2_pre_topc @ sk_A)
% 0.58/0.76        | ~ (l1_pre_topc @ sk_A)
% 0.58/0.76        | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.58/0.76        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.58/0.76        | (v1_xboole_0 @ sk_B_1))),
% 0.58/0.76      inference('sup-', [status(thm)], ['88', '89'])).
% 0.58/0.76  thf('91', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('93', plain,
% 0.58/0.76      (((v2_struct_0 @ sk_A)
% 0.58/0.76        | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.58/0.76        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.58/0.76        | (v1_xboole_0 @ sk_B_1))),
% 0.58/0.76      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.58/0.76  thf('94', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.58/0.76      inference('simpl_trail', [status(thm)], ['7', '64'])).
% 0.58/0.76  thf('95', plain,
% 0.58/0.76      (((v2_struct_0 @ sk_A)
% 0.58/0.76        | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))
% 0.58/0.76        | (v1_xboole_0 @ sk_B_1))),
% 0.58/0.76      inference('demod', [status(thm)], ['93', '94'])).
% 0.58/0.76  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('97', plain,
% 0.58/0.76      (((v1_xboole_0 @ sk_B_1) | (v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.58/0.76      inference('clc', [status(thm)], ['95', '96'])).
% 0.58/0.76  thf('98', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('99', plain, ((v1_tdlat_3 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.58/0.76      inference('clc', [status(thm)], ['97', '98'])).
% 0.58/0.76  thf('100', plain,
% 0.58/0.76      (((v2_struct_0 @ sk_A)
% 0.58/0.76        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.58/0.76        | (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.58/0.76      inference('demod', [status(thm)], ['84', '85', '86', '87', '99'])).
% 0.58/0.76  thf('101', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('102', plain,
% 0.58/0.76      (((v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.58/0.76        | (v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.58/0.76      inference('clc', [status(thm)], ['100', '101'])).
% 0.58/0.76  thf('103', plain,
% 0.58/0.76      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('104', plain,
% 0.58/0.76      (![X33 : $i, X34 : $i]:
% 0.58/0.76         ((v1_xboole_0 @ X33)
% 0.58/0.76          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.58/0.76          | ~ (v2_tex_2 @ X33 @ X34)
% 0.58/0.76          | ((X33) = (u1_struct_0 @ (sk_C @ X33 @ X34)))
% 0.58/0.76          | ~ (l1_pre_topc @ X34)
% 0.58/0.76          | ~ (v2_pre_topc @ X34)
% 0.58/0.76          | (v2_struct_0 @ X34))),
% 0.58/0.76      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.58/0.76  thf('105', plain,
% 0.58/0.76      (((v2_struct_0 @ sk_A)
% 0.58/0.76        | ~ (v2_pre_topc @ sk_A)
% 0.58/0.76        | ~ (l1_pre_topc @ sk_A)
% 0.58/0.76        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.58/0.76        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.58/0.76        | (v1_xboole_0 @ sk_B_1))),
% 0.58/0.76      inference('sup-', [status(thm)], ['103', '104'])).
% 0.58/0.76  thf('106', plain, ((v2_pre_topc @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('108', plain,
% 0.58/0.76      (((v2_struct_0 @ sk_A)
% 0.58/0.76        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.58/0.76        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.58/0.76        | (v1_xboole_0 @ sk_B_1))),
% 0.58/0.76      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.58/0.76  thf('109', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.58/0.76      inference('simpl_trail', [status(thm)], ['7', '64'])).
% 0.58/0.76  thf('110', plain,
% 0.58/0.76      (((v2_struct_0 @ sk_A)
% 0.58/0.76        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.58/0.76        | (v1_xboole_0 @ sk_B_1))),
% 0.58/0.76      inference('demod', [status(thm)], ['108', '109'])).
% 0.58/0.76  thf('111', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('112', plain,
% 0.58/0.76      (((v1_xboole_0 @ sk_B_1)
% 0.58/0.76        | ((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))))),
% 0.58/0.76      inference('clc', [status(thm)], ['110', '111'])).
% 0.58/0.76  thf('113', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('114', plain, (((sk_B_1) = (u1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.58/0.76      inference('clc', [status(thm)], ['112', '113'])).
% 0.58/0.76  thf(fc7_struct_0, axiom,
% 0.58/0.76    (![A:$i]:
% 0.58/0.76     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.58/0.76       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.58/0.76  thf('115', plain,
% 0.58/0.76      (![X25 : $i]:
% 0.58/0.76         ((v1_zfmisc_1 @ (u1_struct_0 @ X25))
% 0.58/0.76          | ~ (l1_struct_0 @ X25)
% 0.58/0.76          | ~ (v7_struct_0 @ X25))),
% 0.58/0.76      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.58/0.76  thf('116', plain,
% 0.58/0.76      (((v1_zfmisc_1 @ sk_B_1)
% 0.58/0.76        | ~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.58/0.76        | ~ (l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.58/0.76      inference('sup+', [status(thm)], ['114', '115'])).
% 0.58/0.76  thf('117', plain,
% 0.58/0.76      ((~ (v1_zfmisc_1 @ sk_B_1)) <= (~ ((v1_zfmisc_1 @ sk_B_1)))),
% 0.58/0.76      inference('split', [status(esa)], ['8'])).
% 0.58/0.76  thf('118', plain, (~ ((v1_zfmisc_1 @ sk_B_1))),
% 0.58/0.76      inference('sat_resolution*', [status(thm)], ['9', '62'])).
% 0.58/0.76  thf('119', plain, (~ (v1_zfmisc_1 @ sk_B_1)),
% 0.58/0.76      inference('simpl_trail', [status(thm)], ['117', '118'])).
% 0.58/0.76  thf('120', plain,
% 0.58/0.76      ((~ (l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))
% 0.58/0.76        | ~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.58/0.76      inference('clc', [status(thm)], ['116', '119'])).
% 0.58/0.76  thf('121', plain, ((m1_pre_topc @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)),
% 0.58/0.76      inference('clc', [status(thm)], ['80', '81'])).
% 0.58/0.76  thf(dt_m1_pre_topc, axiom,
% 0.58/0.76    (![A:$i]:
% 0.58/0.76     ( ( l1_pre_topc @ A ) =>
% 0.58/0.76       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.58/0.76  thf('122', plain,
% 0.58/0.76      (![X23 : $i, X24 : $i]:
% 0.58/0.76         (~ (m1_pre_topc @ X23 @ X24)
% 0.58/0.76          | (l1_pre_topc @ X23)
% 0.58/0.76          | ~ (l1_pre_topc @ X24))),
% 0.58/0.76      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.58/0.76  thf('123', plain,
% 0.58/0.76      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A)))),
% 0.58/0.76      inference('sup-', [status(thm)], ['121', '122'])).
% 0.58/0.76  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 0.58/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.76  thf('125', plain, ((l1_pre_topc @ (sk_C @ sk_B_1 @ sk_A))),
% 0.58/0.76      inference('demod', [status(thm)], ['123', '124'])).
% 0.58/0.76  thf(dt_l1_pre_topc, axiom,
% 0.58/0.76    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.58/0.76  thf('126', plain,
% 0.58/0.76      (![X22 : $i]: ((l1_struct_0 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.58/0.76      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.58/0.76  thf('127', plain, ((l1_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.58/0.76      inference('sup-', [status(thm)], ['125', '126'])).
% 0.58/0.76  thf('128', plain, (~ (v7_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.58/0.76      inference('demod', [status(thm)], ['120', '127'])).
% 0.58/0.76  thf('129', plain, ((v2_struct_0 @ (sk_C @ sk_B_1 @ sk_A))),
% 0.58/0.76      inference('clc', [status(thm)], ['102', '128'])).
% 0.58/0.76  thf('130', plain, ($false), inference('demod', [status(thm)], ['70', '129'])).
% 0.58/0.76  
% 0.58/0.76  % SZS output end Refutation
% 0.58/0.76  
% 0.58/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
