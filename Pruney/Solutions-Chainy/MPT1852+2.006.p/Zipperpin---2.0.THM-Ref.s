%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hfHmnkvBMC

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  159 (1933 expanded)
%              Number of leaves         :   26 ( 555 expanded)
%              Depth                    :   23
%              Number of atoms          : 1224 (21839 expanded)
%              Number of equality atoms :   21 ( 690 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('0',plain,(
    ! [X19: $i] :
      ( ( m1_pre_topc @ X19 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_pre_topc @ X9 @ X8 )
      | ( m1_pre_topc @ X9 @ ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t19_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
              & ( v3_tdlat_3 @ A ) )
           => ( v3_tdlat_3 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                  = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                & ( v3_tdlat_3 @ A ) )
             => ( v3_tdlat_3 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_tex_2])).

thf('4',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ ( g1_pre_topc @ ( u1_struct_0 @ X7 ) @ ( u1_pre_topc @ X7 ) ) )
      | ( m1_pre_topc @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( m1_pre_topc @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( m1_pre_topc @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_pre_topc @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( r1_tarski @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('20',plain,
    ( ( m1_pre_topc @ sk_B_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_pre_topc @ sk_B_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ ( g1_pre_topc @ ( u1_struct_0 @ X7 ) @ ( u1_pre_topc @ X7 ) ) )
      | ( m1_pre_topc @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( r1_tarski @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','30'])).

thf(d3_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) )
             => ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_pre_topc @ A ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ X22 ) @ ( sk_B @ X22 ) ) @ ( u1_pre_topc @ X22 ) )
      | ( v3_tdlat_3 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('33',plain,
    ( ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_B_1 ) )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    m1_pre_topc @ sk_B_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( m1_pre_topc @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('40',plain,(
    m1_pre_topc @ sk_B_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['38','39'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('41',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(t31_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('42',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_2])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('49',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(t78_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_tops_2 @ B @ A )
          <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('50',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_tops_2 @ X17 @ X18 )
      | ( r1_tarski @ X17 @ ( u1_pre_topc @ X18 ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_pre_topc @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( r1_tarski @ ( u1_pre_topc @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('55',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(t35_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v1_tops_2 @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) )
                   => ( ( D = B )
                     => ( v1_tops_2 @ D @ C ) ) ) ) ) ) ) )).

thf('56',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) )
      | ~ ( v1_tops_2 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) )
      | ( v1_tops_2 @ X15 @ X16 )
      | ( X15 != X13 )
      | ~ ( m1_pre_topc @ X16 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t35_tops_2])).

thf('57',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_pre_topc @ X16 @ X14 )
      | ( v1_tops_2 @ X13 @ X16 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_tops_2 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( u1_pre_topc @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( m1_pre_topc @ sk_A @ sk_B_1 )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_A )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['54','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_pre_topc @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('63',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('64',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('65',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( r1_tarski @ X17 @ ( u1_pre_topc @ X18 ) )
      | ( v1_tops_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( v1_tops_2 @ X0 @ sk_B_1 )
      | ~ ( r1_tarski @ X0 @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( v1_tops_2 @ X0 @ sk_B_1 )
      | ~ ( r1_tarski @ X0 @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( r1_tarski @ ( u1_pre_topc @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['69','71'])).

thf('73',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['59','60','61','62','72'])).

thf('74',plain,(
    r1_tarski @ ( u1_pre_topc @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['53','73'])).

thf('75',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('76',plain,
    ( ~ ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_B_1 ) )
    | ( ( u1_pre_topc @ sk_A )
      = ( u1_pre_topc @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_pre_topc @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_pre_topc @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('79',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('84',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('86',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( v1_tops_2 @ X17 @ X18 )
      | ( r1_tarski @ X17 @ ( u1_pre_topc @ X18 ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( r1_tarski @ X0 @ ( u1_pre_topc @ sk_B_1 ) )
      | ~ ( v1_tops_2 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ( r1_tarski @ X0 @ ( u1_pre_topc @ sk_B_1 ) )
      | ~ ( v1_tops_2 @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B_1 )
    | ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X5 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('92',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('93',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('94',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_pre_topc @ X16 @ X14 )
      | ( v1_tops_2 @ X13 @ X16 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) )
      | ~ ( v1_tops_2 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) )
      | ~ ( v1_tops_2 @ X0 @ X1 )
      | ( v1_tops_2 @ X0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ sk_B_1 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B_1 )
      | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B_1 )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['91','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('100',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) )
      | ~ ( r1_tarski @ X17 @ ( u1_pre_topc @ X18 ) )
      | ( v1_tops_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t78_tops_2])).

thf('101',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('104',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['24','25'])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_tops_2 @ ( u1_pre_topc @ sk_A ) @ sk_B_1 ),
    inference(demod,[status(thm)],['97','98','104','105','106'])).

thf('108',plain,(
    r1_tarski @ ( u1_pre_topc @ sk_A ) @ ( u1_pre_topc @ sk_B_1 ) ),
    inference(demod,[status(thm)],['90','107'])).

thf('109',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( u1_pre_topc @ sk_B_1 ) ),
    inference(demod,[status(thm)],['76','108'])).

thf('110',plain,(
    ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','109'])).

thf('111',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('112',plain,(
    ! [X22: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v3_tdlat_3 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('113',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v3_tdlat_3 @ X22 )
      | ~ ( r2_hidden @ X23 @ ( u1_pre_topc @ X22 ) )
      | ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ X22 ) @ X23 ) @ ( u1_pre_topc @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('119',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,
    ( ( u1_pre_topc @ sk_A )
    = ( u1_pre_topc @ sk_B_1 ) ),
    inference(demod,[status(thm)],['76','108'])).

thf('124',plain,(
    ! [X22: $i] :
      ( ( r2_hidden @ ( sk_B @ X22 ) @ ( u1_pre_topc @ X22 ) )
      | ( v3_tdlat_3 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('125',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,(
    ~ ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,(
    r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['122','129'])).

thf('131',plain,(
    $false ),
    inference(demod,[status(thm)],['110','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hfHmnkvBMC
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:03:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 121 iterations in 0.058s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.52  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.52  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 0.21/0.52  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.52  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.21/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.52  thf(t2_tsep_1, axiom,
% 0.21/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (![X19 : $i]: ((m1_pre_topc @ X19 @ X19) | ~ (l1_pre_topc @ X19))),
% 0.21/0.52      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.21/0.52  thf(t65_pre_topc, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( l1_pre_topc @ B ) =>
% 0.21/0.52           ( ( m1_pre_topc @ A @ B ) <=>
% 0.21/0.52             ( m1_pre_topc @
% 0.21/0.52               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X8)
% 0.21/0.52          | ~ (m1_pre_topc @ X9 @ X8)
% 0.21/0.52          | (m1_pre_topc @ X9 @ 
% 0.21/0.52             (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.21/0.52          | ~ (l1_pre_topc @ X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | (m1_pre_topc @ X0 @ 
% 0.21/0.52             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.52          | ~ (l1_pre_topc @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((m1_pre_topc @ X0 @ 
% 0.21/0.52           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.52          | ~ (l1_pre_topc @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.52  thf(t19_tex_2, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( l1_pre_topc @ B ) =>
% 0.21/0.52           ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.21/0.52                 ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.21/0.52               ( v3_tdlat_3 @ A ) ) =>
% 0.21/0.52             ( v3_tdlat_3 @ B ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( l1_pre_topc @ A ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( l1_pre_topc @ B ) =>
% 0.21/0.52              ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.21/0.52                    ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.21/0.52                  ( v3_tdlat_3 @ A ) ) =>
% 0.21/0.52                ( v3_tdlat_3 @ B ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t19_tex_2])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.52         = (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t59_pre_topc, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_pre_topc @
% 0.21/0.52             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.21/0.52           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X6 : $i, X7 : $i]:
% 0.21/0.52         (~ (m1_pre_topc @ X6 @ 
% 0.21/0.52             (g1_pre_topc @ (u1_struct_0 @ X7) @ (u1_pre_topc @ X7)))
% 0.21/0.52          | (m1_pre_topc @ X6 @ X7)
% 0.21/0.52          | ~ (l1_pre_topc @ X7))),
% 0.21/0.52      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_pre_topc @ X0 @ 
% 0.21/0.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.52          | ~ (l1_pre_topc @ sk_B_1)
% 0.21/0.52          | (m1_pre_topc @ X0 @ sk_B_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.52  thf('7', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_pre_topc @ X0 @ 
% 0.21/0.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.52          | (m1_pre_topc @ X0 @ sk_B_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.52  thf('9', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_A @ sk_B_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['3', '8'])).
% 0.21/0.52  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('11', plain, ((m1_pre_topc @ sk_A @ sk_B_1)),
% 0.21/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf(t35_borsuk_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.52           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i]:
% 0.21/0.52         (~ (m1_pre_topc @ X20 @ X21)
% 0.21/0.52          | (r1_tarski @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))
% 0.21/0.52          | ~ (l1_pre_topc @ X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_B_1)
% 0.21/0.52        | (r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf('14', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      ((r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf(d10_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X0 : $i, X2 : $i]:
% 0.21/0.52         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      ((~ (r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.21/0.52        | ((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.21/0.52         = (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((m1_pre_topc @ X0 @ 
% 0.21/0.52           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.52          | ~ (l1_pre_topc @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (((m1_pre_topc @ sk_B_1 @ 
% 0.21/0.52         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.52        | ~ (l1_pre_topc @ sk_B_1))),
% 0.21/0.52      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.52  thf('21', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      ((m1_pre_topc @ sk_B_1 @ 
% 0.21/0.52        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X6 : $i, X7 : $i]:
% 0.21/0.52         (~ (m1_pre_topc @ X6 @ 
% 0.21/0.52             (g1_pre_topc @ (u1_struct_0 @ X7) @ (u1_pre_topc @ X7)))
% 0.21/0.52          | (m1_pre_topc @ X6 @ X7)
% 0.21/0.52          | ~ (l1_pre_topc @ X7))),
% 0.21/0.52      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.21/0.52  thf('24', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B_1 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.52  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('26', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i]:
% 0.21/0.52         (~ (m1_pre_topc @ X20 @ X21)
% 0.21/0.52          | (r1_tarski @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))
% 0.21/0.52          | ~ (l1_pre_topc @ X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | (r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      ((r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.52  thf('31', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['17', '30'])).
% 0.21/0.52  thf(d3_tdlat_3, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ( v3_tdlat_3 @ A ) <=>
% 0.21/0.52         ( ![B:$i]:
% 0.21/0.52           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52             ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) =>
% 0.21/0.52               ( r2_hidden @
% 0.21/0.52                 ( k6_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.21/0.52                 ( u1_pre_topc @ A ) ) ) ) ) ) ))).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (![X22 : $i]:
% 0.21/0.52         (~ (r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ X22) @ (sk_B @ X22)) @ 
% 0.21/0.52             (u1_pre_topc @ X22))
% 0.21/0.52          | (v3_tdlat_3 @ X22)
% 0.21/0.52          | ~ (l1_pre_topc @ X22))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      ((~ (r2_hidden @ 
% 0.21/0.52           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.21/0.52           (u1_pre_topc @ sk_B_1))
% 0.21/0.52        | ~ (l1_pre_topc @ sk_B_1)
% 0.21/0.52        | (v3_tdlat_3 @ sk_B_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.52  thf('34', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      ((~ (r2_hidden @ 
% 0.21/0.52           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.21/0.52           (u1_pre_topc @ sk_B_1))
% 0.21/0.52        | (v3_tdlat_3 @ sk_B_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('36', plain, (~ (v3_tdlat_3 @ sk_B_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      (~ (r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.21/0.52          (u1_pre_topc @ sk_B_1))),
% 0.21/0.52      inference('clc', [status(thm)], ['35', '36'])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      ((m1_pre_topc @ sk_B_1 @ 
% 0.21/0.52        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_pre_topc @ X0 @ 
% 0.21/0.52             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.52          | (m1_pre_topc @ X0 @ sk_B_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.52  thf('40', plain, ((m1_pre_topc @ sk_B_1 @ sk_B_1)),
% 0.21/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.52  thf(dt_u1_pre_topc, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( m1_subset_1 @
% 0.21/0.52         ( u1_pre_topc @ A ) @ 
% 0.21/0.52         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (![X5 : $i]:
% 0.21/0.52         ((m1_subset_1 @ (u1_pre_topc @ X5) @ 
% 0.21/0.52           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.21/0.52          | ~ (l1_pre_topc @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.52  thf(t31_tops_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m1_subset_1 @
% 0.21/0.52                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.21/0.52               ( m1_subset_1 @
% 0.21/0.52                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.52         (~ (m1_pre_topc @ X10 @ X11)
% 0.21/0.52          | (m1_subset_1 @ X12 @ 
% 0.21/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11))))
% 0.21/0.52          | ~ (m1_subset_1 @ X12 @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.21/0.52          | ~ (l1_pre_topc @ X11))),
% 0.21/0.52      inference('cnf', [status(esa)], [t31_tops_2])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X1)
% 0.21/0.52          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.21/0.52          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (((m1_subset_1 @ (u1_pre_topc @ sk_B_1) @ 
% 0.21/0.52         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1))))
% 0.21/0.52        | ~ (l1_pre_topc @ sk_B_1)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_B_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['40', '43'])).
% 0.21/0.52  thf('45', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('46', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      ((m1_subset_1 @ (u1_pre_topc @ sk_B_1) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1))))),
% 0.21/0.52      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.21/0.52  thf('48', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['17', '30'])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      ((m1_subset_1 @ (u1_pre_topc @ sk_B_1) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.52  thf(t78_tops_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @
% 0.21/0.52             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.52           ( ( v1_tops_2 @ B @ A ) <=> ( r1_tarski @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (![X17 : $i, X18 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X17 @ 
% 0.21/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18))))
% 0.21/0.52          | ~ (v1_tops_2 @ X17 @ X18)
% 0.21/0.52          | (r1_tarski @ X17 @ (u1_pre_topc @ X18))
% 0.21/0.52          | ~ (l1_pre_topc @ X18))),
% 0.21/0.52      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | (r1_tarski @ (u1_pre_topc @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.21/0.52        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.52  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (((r1_tarski @ (u1_pre_topc @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.21/0.52        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      (![X5 : $i]:
% 0.21/0.52         ((m1_subset_1 @ (u1_pre_topc @ X5) @ 
% 0.21/0.52           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.21/0.52          | ~ (l1_pre_topc @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.52  thf('55', plain,
% 0.21/0.52      ((m1_subset_1 @ (u1_pre_topc @ sk_B_1) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.52  thf(t35_tops_2, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @
% 0.21/0.52             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.52               ( ( v1_tops_2 @ B @ A ) =>
% 0.21/0.52                 ( ![D:$i]:
% 0.21/0.52                   ( ( m1_subset_1 @
% 0.21/0.52                       D @ 
% 0.21/0.52                       ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) ) =>
% 0.21/0.52                     ( ( ( D ) = ( B ) ) => ( v1_tops_2 @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('56', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X13 @ 
% 0.21/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14))))
% 0.21/0.52          | ~ (v1_tops_2 @ X13 @ X14)
% 0.21/0.52          | ~ (m1_subset_1 @ X15 @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))
% 0.21/0.52          | (v1_tops_2 @ X15 @ X16)
% 0.21/0.52          | ((X15) != (X13))
% 0.21/0.52          | ~ (m1_pre_topc @ X16 @ X14)
% 0.21/0.52          | ~ (l1_pre_topc @ X14))),
% 0.21/0.52      inference('cnf', [status(esa)], [t35_tops_2])).
% 0.21/0.52  thf('57', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X14)
% 0.21/0.52          | ~ (m1_pre_topc @ X16 @ X14)
% 0.21/0.52          | (v1_tops_2 @ X13 @ X16)
% 0.21/0.52          | ~ (m1_subset_1 @ X13 @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))
% 0.21/0.52          | ~ (v1_tops_2 @ X13 @ X14)
% 0.21/0.52          | ~ (m1_subset_1 @ X13 @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['56'])).
% 0.21/0.52  thf('58', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ (u1_pre_topc @ sk_B_1) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 0.21/0.52          | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ X0)
% 0.21/0.52          | (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_A)
% 0.21/0.52          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['55', '57'])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_B_1)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_B_1)
% 0.21/0.52        | ~ (m1_pre_topc @ sk_A @ sk_B_1)
% 0.21/0.52        | (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_A)
% 0.21/0.52        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_B_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['54', '58'])).
% 0.21/0.52  thf('60', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('61', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('62', plain, ((m1_pre_topc @ sk_A @ sk_B_1)),
% 0.21/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('63', plain,
% 0.21/0.52      ((m1_subset_1 @ (u1_pre_topc @ sk_B_1) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.52  thf('64', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['17', '30'])).
% 0.21/0.52  thf('65', plain,
% 0.21/0.52      (![X17 : $i, X18 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X17 @ 
% 0.21/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18))))
% 0.21/0.52          | ~ (r1_tarski @ X17 @ (u1_pre_topc @ X18))
% 0.21/0.52          | (v1_tops_2 @ X17 @ X18)
% 0.21/0.52          | ~ (l1_pre_topc @ X18))),
% 0.21/0.52      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.21/0.52  thf('66', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ 
% 0.21/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.52          | ~ (l1_pre_topc @ sk_B_1)
% 0.21/0.52          | (v1_tops_2 @ X0 @ sk_B_1)
% 0.21/0.52          | ~ (r1_tarski @ X0 @ (u1_pre_topc @ sk_B_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.52  thf('67', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('68', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ 
% 0.21/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.52          | (v1_tops_2 @ X0 @ sk_B_1)
% 0.21/0.52          | ~ (r1_tarski @ X0 @ (u1_pre_topc @ sk_B_1)))),
% 0.21/0.52      inference('demod', [status(thm)], ['66', '67'])).
% 0.21/0.52  thf('69', plain,
% 0.21/0.52      ((~ (r1_tarski @ (u1_pre_topc @ sk_B_1) @ (u1_pre_topc @ sk_B_1))
% 0.21/0.52        | (v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_B_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['63', '68'])).
% 0.21/0.52  thf('70', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.52  thf('71', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.52      inference('simplify', [status(thm)], ['70'])).
% 0.21/0.52  thf('72', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_B_1)),
% 0.21/0.52      inference('demod', [status(thm)], ['69', '71'])).
% 0.21/0.52  thf('73', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_B_1) @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['59', '60', '61', '62', '72'])).
% 0.21/0.52  thf('74', plain,
% 0.21/0.52      ((r1_tarski @ (u1_pre_topc @ sk_B_1) @ (u1_pre_topc @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['53', '73'])).
% 0.21/0.52  thf('75', plain,
% 0.21/0.52      (![X0 : $i, X2 : $i]:
% 0.21/0.52         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.52  thf('76', plain,
% 0.21/0.52      ((~ (r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_B_1))
% 0.21/0.52        | ((u1_pre_topc @ sk_A) = (u1_pre_topc @ sk_B_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['74', '75'])).
% 0.21/0.52  thf('77', plain, ((m1_pre_topc @ sk_A @ sk_B_1)),
% 0.21/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('78', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X1)
% 0.21/0.52          | (m1_subset_1 @ (u1_pre_topc @ X0) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.21/0.52          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.52  thf('79', plain,
% 0.21/0.52      (((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.21/0.52         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1))))
% 0.21/0.52        | ~ (l1_pre_topc @ sk_B_1)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['77', '78'])).
% 0.21/0.52  thf('80', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('82', plain,
% 0.21/0.52      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B_1))))),
% 0.21/0.52      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.21/0.52  thf('83', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['17', '30'])).
% 0.21/0.52  thf('84', plain,
% 0.21/0.52      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['82', '83'])).
% 0.21/0.52  thf('85', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['17', '30'])).
% 0.21/0.52  thf('86', plain,
% 0.21/0.52      (![X17 : $i, X18 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X17 @ 
% 0.21/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18))))
% 0.21/0.52          | ~ (v1_tops_2 @ X17 @ X18)
% 0.21/0.52          | (r1_tarski @ X17 @ (u1_pre_topc @ X18))
% 0.21/0.52          | ~ (l1_pre_topc @ X18))),
% 0.21/0.52      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.21/0.52  thf('87', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ 
% 0.21/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.52          | ~ (l1_pre_topc @ sk_B_1)
% 0.21/0.52          | (r1_tarski @ X0 @ (u1_pre_topc @ sk_B_1))
% 0.21/0.52          | ~ (v1_tops_2 @ X0 @ sk_B_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['85', '86'])).
% 0.21/0.52  thf('88', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('89', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ 
% 0.21/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.52          | (r1_tarski @ X0 @ (u1_pre_topc @ sk_B_1))
% 0.21/0.52          | ~ (v1_tops_2 @ X0 @ sk_B_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['87', '88'])).
% 0.21/0.52  thf('90', plain,
% 0.21/0.52      ((~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B_1)
% 0.21/0.52        | (r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_B_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['84', '89'])).
% 0.21/0.52  thf('91', plain,
% 0.21/0.52      (![X5 : $i]:
% 0.21/0.52         ((m1_subset_1 @ (u1_pre_topc @ X5) @ 
% 0.21/0.52           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5))))
% 0.21/0.52          | ~ (l1_pre_topc @ X5))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.52  thf('92', plain,
% 0.21/0.52      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['82', '83'])).
% 0.21/0.52  thf('93', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['17', '30'])).
% 0.21/0.52  thf('94', plain,
% 0.21/0.52      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X14)
% 0.21/0.52          | ~ (m1_pre_topc @ X16 @ X14)
% 0.21/0.52          | (v1_tops_2 @ X13 @ X16)
% 0.21/0.52          | ~ (m1_subset_1 @ X13 @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))
% 0.21/0.52          | ~ (v1_tops_2 @ X13 @ X14)
% 0.21/0.52          | ~ (m1_subset_1 @ X13 @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['56'])).
% 0.21/0.52  thf('95', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ 
% 0.21/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))
% 0.21/0.52          | ~ (v1_tops_2 @ X0 @ X1)
% 0.21/0.52          | (v1_tops_2 @ X0 @ sk_B_1)
% 0.21/0.52          | ~ (m1_pre_topc @ sk_B_1 @ X1)
% 0.21/0.52          | ~ (l1_pre_topc @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['93', '94'])).
% 0.21/0.52  thf('96', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X0)
% 0.21/0.52          | ~ (m1_pre_topc @ sk_B_1 @ X0)
% 0.21/0.52          | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B_1)
% 0.21/0.52          | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ X0)
% 0.21/0.52          | ~ (m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.21/0.52               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['92', '95'])).
% 0.21/0.52  thf('97', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | ~ (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)
% 0.21/0.52        | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B_1)
% 0.21/0.52        | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['91', '96'])).
% 0.21/0.52  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('99', plain,
% 0.21/0.52      ((m1_subset_1 @ (u1_pre_topc @ sk_A) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['82', '83'])).
% 0.21/0.52  thf('100', plain,
% 0.21/0.52      (![X17 : $i, X18 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X17 @ 
% 0.21/0.52             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18))))
% 0.21/0.52          | ~ (r1_tarski @ X17 @ (u1_pre_topc @ X18))
% 0.21/0.52          | (v1_tops_2 @ X17 @ X18)
% 0.21/0.52          | ~ (l1_pre_topc @ X18))),
% 0.21/0.52      inference('cnf', [status(esa)], [t78_tops_2])).
% 0.21/0.52  thf('101', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | (v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)
% 0.21/0.52        | ~ (r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['99', '100'])).
% 0.21/0.52  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('103', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.52      inference('simplify', [status(thm)], ['70'])).
% 0.21/0.52  thf('104', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['101', '102', '103'])).
% 0.21/0.52  thf('105', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.21/0.52      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.52  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('107', plain, ((v1_tops_2 @ (u1_pre_topc @ sk_A) @ sk_B_1)),
% 0.21/0.52      inference('demod', [status(thm)], ['97', '98', '104', '105', '106'])).
% 0.21/0.52  thf('108', plain,
% 0.21/0.52      ((r1_tarski @ (u1_pre_topc @ sk_A) @ (u1_pre_topc @ sk_B_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['90', '107'])).
% 0.21/0.52  thf('109', plain, (((u1_pre_topc @ sk_A) = (u1_pre_topc @ sk_B_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['76', '108'])).
% 0.21/0.52  thf('110', plain,
% 0.21/0.52      (~ (r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.21/0.52          (u1_pre_topc @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['37', '109'])).
% 0.21/0.52  thf('111', plain, (((u1_struct_0 @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['17', '30'])).
% 0.21/0.52  thf('112', plain,
% 0.21/0.52      (![X22 : $i]:
% 0.21/0.52         ((m1_subset_1 @ (sk_B @ X22) @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.21/0.52          | (v3_tdlat_3 @ X22)
% 0.21/0.52          | ~ (l1_pre_topc @ X22))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.21/0.52  thf('113', plain,
% 0.21/0.52      (((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52        | ~ (l1_pre_topc @ sk_B_1)
% 0.21/0.52        | (v3_tdlat_3 @ sk_B_1))),
% 0.21/0.52      inference('sup+', [status(thm)], ['111', '112'])).
% 0.21/0.52  thf('114', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('115', plain,
% 0.21/0.52      (((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52        | (v3_tdlat_3 @ sk_B_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['113', '114'])).
% 0.21/0.52  thf('116', plain, (~ (v3_tdlat_3 @ sk_B_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('117', plain,
% 0.21/0.52      ((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('clc', [status(thm)], ['115', '116'])).
% 0.21/0.52  thf('118', plain,
% 0.21/0.52      (![X22 : $i, X23 : $i]:
% 0.21/0.52         (~ (v3_tdlat_3 @ X22)
% 0.21/0.52          | ~ (r2_hidden @ X23 @ (u1_pre_topc @ X22))
% 0.21/0.52          | (r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ X22) @ X23) @ 
% 0.21/0.52             (u1_pre_topc @ X22))
% 0.21/0.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.21/0.52          | ~ (l1_pre_topc @ X22))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.21/0.52  thf('119', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | (r2_hidden @ 
% 0.21/0.52           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.21/0.52           (u1_pre_topc @ sk_A))
% 0.21/0.52        | ~ (r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.21/0.52        | ~ (v3_tdlat_3 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['117', '118'])).
% 0.21/0.52  thf('120', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('121', plain, ((v3_tdlat_3 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('122', plain,
% 0.21/0.52      (((r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.21/0.52         (u1_pre_topc @ sk_A))
% 0.21/0.52        | ~ (r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['119', '120', '121'])).
% 0.21/0.52  thf('123', plain, (((u1_pre_topc @ sk_A) = (u1_pre_topc @ sk_B_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['76', '108'])).
% 0.21/0.52  thf('124', plain,
% 0.21/0.52      (![X22 : $i]:
% 0.21/0.52         ((r2_hidden @ (sk_B @ X22) @ (u1_pre_topc @ X22))
% 0.21/0.52          | (v3_tdlat_3 @ X22)
% 0.21/0.52          | ~ (l1_pre_topc @ X22))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.21/0.52  thf('125', plain,
% 0.21/0.52      (((r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.21/0.52        | ~ (l1_pre_topc @ sk_B_1)
% 0.21/0.52        | (v3_tdlat_3 @ sk_B_1))),
% 0.21/0.52      inference('sup+', [status(thm)], ['123', '124'])).
% 0.21/0.52  thf('126', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('127', plain,
% 0.21/0.52      (((r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.21/0.52        | (v3_tdlat_3 @ sk_B_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['125', '126'])).
% 0.21/0.52  thf('128', plain, (~ (v3_tdlat_3 @ sk_B_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('129', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))),
% 0.21/0.52      inference('clc', [status(thm)], ['127', '128'])).
% 0.21/0.52  thf('130', plain,
% 0.21/0.52      ((r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.21/0.52        (u1_pre_topc @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['122', '129'])).
% 0.21/0.52  thf('131', plain, ($false), inference('demod', [status(thm)], ['110', '130'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
