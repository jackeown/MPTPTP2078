%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.T8aCX6GLvF

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  143 (3004 expanded)
%              Number of leaves         :   26 ( 853 expanded)
%              Depth                    :   27
%              Number of atoms          : 1141 (33734 expanded)
%              Number of equality atoms :   16 (1068 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

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

thf('0',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('1',plain,(
    ! [X22: $i] :
      ( ( m1_pre_topc @ X22 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( m1_pre_topc @ X17 @ ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( m1_pre_topc @ sk_B_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['0','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_pre_topc @ sk_B_1 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ( m1_pre_topc @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['9','10'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( r1_tarski @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
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
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('19',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ( m1_pre_topc @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( m1_pre_topc @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( m1_pre_topc @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_pre_topc @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( r1_tarski @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('28',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B_1 ) ),
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
    ! [X25: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v3_tdlat_3 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('33',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v3_tdlat_3 @ X25 )
      | ~ ( r2_hidden @ X26 @ ( u1_pre_topc @ X25 ) )
      | ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ X25 ) @ X26 ) @ ( u1_pre_topc @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf(d5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('44',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v3_pre_topc @ X6 @ X7 )
      | ( r2_hidden @ X6 @ ( u1_pre_topc @ X7 ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) )
    | ~ ( v3_pre_topc @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('49',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf(t33_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v3_pre_topc @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                   => ( ( D = B )
                     => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) )).

thf('50',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v3_pre_topc @ X20 @ X21 )
      | ( X20 != X18 )
      | ~ ( m1_pre_topc @ X21 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t33_tops_2])).

thf('51',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_pre_topc @ X21 @ X19 )
      | ( v3_pre_topc @ X18 @ X21 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ ( sk_B @ sk_B_1 ) @ X0 )
      | ( v3_pre_topc @ ( sk_B @ sk_B_1 ) @ sk_A )
      | ~ ( m1_pre_topc @ sk_A @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,
    ( ~ ( m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ~ ( m1_pre_topc @ sk_A @ sk_B_1 )
    | ( v3_pre_topc @ ( sk_B @ sk_B_1 ) @ sk_A )
    | ~ ( v3_pre_topc @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf('54',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('55',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_pre_topc @ sk_A @ sk_B_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('57',plain,(
    ! [X25: $i] :
      ( ( r2_hidden @ ( sk_B @ X25 ) @ ( u1_pre_topc @ X25 ) )
      | ( v3_tdlat_3 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('58',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('59',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( r2_hidden @ X6 @ ( u1_pre_topc @ X7 ) )
      | ( v3_pre_topc @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( v3_pre_topc @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['17','30'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('64',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('65',plain,
    ( ( m1_subset_1 @ ( u1_pre_topc @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ ( u1_pre_topc @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('68',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B_1 ) )
      | ( v3_pre_topc @ X0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['62','69'])).

thf('71',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
    | ( v3_tdlat_3 @ sk_B_1 )
    | ( v3_pre_topc @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['57','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v3_tdlat_3 @ sk_B_1 )
    | ( v3_pre_topc @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v3_pre_topc @ ( sk_B @ sk_B_1 ) @ sk_B_1 ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    v3_pre_topc @ ( sk_B @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['53','54','55','56','75'])).

thf('77',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['47','76'])).

thf('78',plain,(
    r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['42','77'])).

thf('79',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('80',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_pre_topc @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( m1_subset_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('86',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v3_pre_topc @ X6 @ X7 )
      | ( r2_hidden @ X6 @ ( u1_pre_topc @ X7 ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B_1 )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B_1 ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( u1_pre_topc @ sk_B_1 ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( v3_pre_topc @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 )
    | ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('92',plain,(
    ! [X25: $i] :
      ( ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ X25 ) @ ( sk_B @ X25 ) ) @ ( u1_pre_topc @ X25 ) )
      | ( v3_tdlat_3 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_tdlat_3])).

thf('93',plain,
    ( ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_B_1 )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_B_1 ) )
    | ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v3_tdlat_3 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v3_pre_topc @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['90','97'])).

thf('99',plain,(
    m1_subset_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('100',plain,(
    m1_subset_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('101',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['17','30'])).

thf('102',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_pre_topc @ X21 @ X19 )
      | ( v3_pre_topc @ X18 @ X21 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v3_pre_topc @ X0 @ X1 )
      | ( v3_pre_topc @ X0 @ sk_B_1 )
      | ~ ( m1_pre_topc @ sk_B_1 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 )
      | ( v3_pre_topc @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 )
      | ~ ( v3_pre_topc @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ X0 )
      | ~ ( m1_subset_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,
    ( ~ ( v3_pre_topc @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ( v3_pre_topc @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 )
    | ~ ( m1_pre_topc @ sk_B_1 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['99','104'])).

thf('106',plain,(
    m1_subset_1 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('107',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( r2_hidden @ X6 @ ( u1_pre_topc @ X7 ) )
      | ( v3_pre_topc @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_pre_topc])).

thf('108',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A )
    | ~ ( r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    r2_hidden @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( u1_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['42','77'])).

thf('111',plain,(
    v3_pre_topc @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_A ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['9','10'])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v3_pre_topc @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ sk_B_1 ),
    inference(demod,[status(thm)],['105','111','112','113'])).

thf('115',plain,(
    $false ),
    inference(demod,[status(thm)],['98','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.T8aCX6GLvF
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.20/0.34  % DateTime   : Tue Dec  1 19:27:57 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 129 iterations in 0.071s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.53  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 0.20/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.20/0.53  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.20/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.53  thf(t19_tex_2, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( l1_pre_topc @ B ) =>
% 0.20/0.53           ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.53                 ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.20/0.53               ( v3_tdlat_3 @ A ) ) =>
% 0.20/0.53             ( v3_tdlat_3 @ B ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( l1_pre_topc @ A ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( l1_pre_topc @ B ) =>
% 0.20/0.53              ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.20/0.53                    ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.20/0.53                  ( v3_tdlat_3 @ A ) ) =>
% 0.20/0.53                ( v3_tdlat_3 @ B ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t19_tex_2])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.53         = (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t2_tsep_1, axiom,
% 0.20/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X22 : $i]: ((m1_pre_topc @ X22 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.20/0.53      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.20/0.53  thf(t65_pre_topc, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( l1_pre_topc @ B ) =>
% 0.20/0.53           ( ( m1_pre_topc @ A @ B ) <=>
% 0.20/0.53             ( m1_pre_topc @
% 0.20/0.53               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X16)
% 0.20/0.53          | ~ (m1_pre_topc @ X17 @ X16)
% 0.20/0.53          | (m1_pre_topc @ X17 @ 
% 0.20/0.53             (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)))
% 0.20/0.53          | ~ (l1_pre_topc @ X17))),
% 0.20/0.53      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X0)
% 0.20/0.53          | ~ (l1_pre_topc @ X0)
% 0.20/0.53          | (m1_pre_topc @ X0 @ 
% 0.20/0.53             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.53          | ~ (l1_pre_topc @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((m1_pre_topc @ X0 @ 
% 0.20/0.53           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.53          | ~ (l1_pre_topc @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (((m1_pre_topc @ sk_B_1 @ 
% 0.20/0.53         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.53        | ~ (l1_pre_topc @ sk_B_1))),
% 0.20/0.53      inference('sup+', [status(thm)], ['0', '4'])).
% 0.20/0.53  thf('6', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      ((m1_pre_topc @ sk_B_1 @ 
% 0.20/0.53        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.53  thf(t59_pre_topc, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_pre_topc @
% 0.20/0.53             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.20/0.53           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X14 @ 
% 0.20/0.53             (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 0.20/0.53          | (m1_pre_topc @ X14 @ X15)
% 0.20/0.53          | ~ (l1_pre_topc @ X15))),
% 0.20/0.53      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.20/0.53  thf('9', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('11', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.20/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf(t35_borsuk_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.53           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X23 : $i, X24 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X23 @ X24)
% 0.20/0.53          | (r1_tarski @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X24))
% 0.20/0.53          | ~ (l1_pre_topc @ X24))),
% 0.20/0.53      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | (r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.53  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      ((r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf(d10_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X0 : $i, X2 : $i]:
% 0.20/0.53         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      ((~ (r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))
% 0.20/0.53        | ((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((m1_pre_topc @ X0 @ 
% 0.20/0.53           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.53          | ~ (l1_pre_topc @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.20/0.53         = (g1_pre_topc @ (u1_struct_0 @ sk_B_1) @ (u1_pre_topc @ sk_B_1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X14 @ 
% 0.20/0.53             (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 0.20/0.53          | (m1_pre_topc @ X14 @ X15)
% 0.20/0.53          | ~ (l1_pre_topc @ X15))),
% 0.20/0.53      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X0 @ 
% 0.20/0.53             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.53          | ~ (l1_pre_topc @ sk_B_1)
% 0.20/0.53          | (m1_pre_topc @ X0 @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf('22', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X0 @ 
% 0.20/0.53             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.53          | (m1_pre_topc @ X0 @ sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf('24', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_A @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '23'])).
% 0.20/0.53  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('26', plain, ((m1_pre_topc @ sk_A @ sk_B_1)),
% 0.20/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X23 : $i, X24 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X23 @ X24)
% 0.20/0.53          | (r1_tarski @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X24))
% 0.20/0.53          | ~ (l1_pre_topc @ X24))),
% 0.20/0.53      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_B_1)
% 0.20/0.53        | (r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('29', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      ((r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('31', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['17', '30'])).
% 0.20/0.53  thf(d3_tdlat_3, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ( v3_tdlat_3 @ A ) <=>
% 0.20/0.53         ( ![B:$i]:
% 0.20/0.53           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53             ( ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) =>
% 0.20/0.53               ( r2_hidden @
% 0.20/0.53                 ( k6_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.20/0.53                 ( u1_pre_topc @ A ) ) ) ) ) ) ))).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X25 : $i]:
% 0.20/0.53         ((m1_subset_1 @ (sk_B @ X25) @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.20/0.53          | (v3_tdlat_3 @ X25)
% 0.20/0.53          | ~ (l1_pre_topc @ X25))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53        | ~ (l1_pre_topc @ sk_B_1)
% 0.20/0.53        | (v3_tdlat_3 @ sk_B_1))),
% 0.20/0.53      inference('sup+', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf('34', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53        | (v3_tdlat_3 @ sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('36', plain, (~ (v3_tdlat_3 @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      ((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (![X25 : $i, X26 : $i]:
% 0.20/0.53         (~ (v3_tdlat_3 @ X25)
% 0.20/0.53          | ~ (r2_hidden @ X26 @ (u1_pre_topc @ X25))
% 0.20/0.53          | (r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ X25) @ X26) @ 
% 0.20/0.53             (u1_pre_topc @ X25))
% 0.20/0.53          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.20/0.53          | ~ (l1_pre_topc @ X25))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | (r2_hidden @ 
% 0.20/0.53           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.53           (u1_pre_topc @ sk_A))
% 0.20/0.53        | ~ (r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.20/0.53        | ~ (v3_tdlat_3 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('41', plain, ((v3_tdlat_3 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (((r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.53         (u1_pre_topc @ sk_A))
% 0.20/0.53        | ~ (r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      ((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.53  thf(d5_pre_topc, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ( v3_pre_topc @ B @ A ) <=>
% 0.20/0.53             ( r2_hidden @ B @ ( u1_pre_topc @ A ) ) ) ) ) ))).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.53          | ~ (v3_pre_topc @ X6 @ X7)
% 0.20/0.53          | (r2_hidden @ X6 @ (u1_pre_topc @ X7))
% 0.20/0.53          | ~ (l1_pre_topc @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | (r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.20/0.53        | ~ (v3_pre_topc @ (sk_B @ sk_B_1) @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.53  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (((r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))
% 0.20/0.53        | ~ (v3_pre_topc @ (sk_B @ sk_B_1) @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.53  thf('48', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['17', '30'])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      ((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.53  thf(t33_tops_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53           ( ![C:$i]:
% 0.20/0.53             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.53               ( ( v3_pre_topc @ B @ A ) =>
% 0.20/0.53                 ( ![D:$i]:
% 0.20/0.53                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.20/0.53                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.53          | ~ (v3_pre_topc @ X18 @ X19)
% 0.20/0.53          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.53          | (v3_pre_topc @ X20 @ X21)
% 0.20/0.53          | ((X20) != (X18))
% 0.20/0.53          | ~ (m1_pre_topc @ X21 @ X19)
% 0.20/0.53          | ~ (l1_pre_topc @ X19))),
% 0.20/0.53      inference('cnf', [status(esa)], [t33_tops_2])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i, X21 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X19)
% 0.20/0.53          | ~ (m1_pre_topc @ X21 @ X19)
% 0.20/0.53          | (v3_pre_topc @ X18 @ X21)
% 0.20/0.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.53          | ~ (v3_pre_topc @ X18 @ X19)
% 0.20/0.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.53          | ~ (v3_pre_topc @ (sk_B @ sk_B_1) @ X0)
% 0.20/0.53          | (v3_pre_topc @ (sk_B @ sk_B_1) @ sk_A)
% 0.20/0.53          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.20/0.53          | ~ (l1_pre_topc @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['49', '51'])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      ((~ (m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53        | ~ (l1_pre_topc @ sk_B_1)
% 0.20/0.53        | ~ (m1_pre_topc @ sk_A @ sk_B_1)
% 0.20/0.53        | (v3_pre_topc @ (sk_B @ sk_B_1) @ sk_A)
% 0.20/0.53        | ~ (v3_pre_topc @ (sk_B @ sk_B_1) @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['48', '52'])).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      ((m1_subset_1 @ (sk_B @ sk_B_1) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.53  thf('55', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('56', plain, ((m1_pre_topc @ sk_A @ sk_B_1)),
% 0.20/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (![X25 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_B @ X25) @ (u1_pre_topc @ X25))
% 0.20/0.53          | (v3_tdlat_3 @ X25)
% 0.20/0.53          | ~ (l1_pre_topc @ X25))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.20/0.53  thf('58', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['17', '30'])).
% 0.20/0.53  thf('59', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.53          | ~ (r2_hidden @ X6 @ (u1_pre_topc @ X7))
% 0.20/0.53          | (v3_pre_topc @ X6 @ X7)
% 0.20/0.53          | ~ (l1_pre_topc @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | ~ (l1_pre_topc @ sk_B_1)
% 0.20/0.53          | (v3_pre_topc @ X0 @ sk_B_1)
% 0.20/0.53          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_B_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.53  thf('61', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | (v3_pre_topc @ X0 @ sk_B_1)
% 0.20/0.53          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_B_1)))),
% 0.20/0.53      inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.53  thf('63', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['17', '30'])).
% 0.20/0.53  thf(dt_u1_pre_topc, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( m1_subset_1 @
% 0.20/0.53         ( u1_pre_topc @ A ) @ 
% 0.20/0.53         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.53  thf('64', plain,
% 0.20/0.53      (![X10 : $i]:
% 0.20/0.53         ((m1_subset_1 @ (u1_pre_topc @ X10) @ 
% 0.20/0.53           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.20/0.53          | ~ (l1_pre_topc @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.53  thf('65', plain,
% 0.20/0.53      (((m1_subset_1 @ (u1_pre_topc @ sk_B_1) @ 
% 0.20/0.53         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.53        | ~ (l1_pre_topc @ sk_B_1))),
% 0.20/0.53      inference('sup+', [status(thm)], ['63', '64'])).
% 0.20/0.53  thf('66', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('67', plain,
% 0.20/0.53      ((m1_subset_1 @ (u1_pre_topc @ sk_B_1) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.53  thf(t4_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.20/0.53       ( m1_subset_1 @ A @ C ) ))).
% 0.20/0.53  thf('68', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.53          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.20/0.53          | (m1_subset_1 @ X3 @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_B_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['67', '68'])).
% 0.20/0.53  thf('70', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ (u1_pre_topc @ sk_B_1))
% 0.20/0.53          | (v3_pre_topc @ X0 @ sk_B_1))),
% 0.20/0.53      inference('clc', [status(thm)], ['62', '69'])).
% 0.20/0.53  thf('71', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_B_1)
% 0.20/0.53        | (v3_tdlat_3 @ sk_B_1)
% 0.20/0.53        | (v3_pre_topc @ (sk_B @ sk_B_1) @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['57', '70'])).
% 0.20/0.53  thf('72', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('73', plain,
% 0.20/0.53      (((v3_tdlat_3 @ sk_B_1) | (v3_pre_topc @ (sk_B @ sk_B_1) @ sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['71', '72'])).
% 0.20/0.53  thf('74', plain, (~ (v3_tdlat_3 @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('75', plain, ((v3_pre_topc @ (sk_B @ sk_B_1) @ sk_B_1)),
% 0.20/0.53      inference('clc', [status(thm)], ['73', '74'])).
% 0.20/0.53  thf('76', plain, ((v3_pre_topc @ (sk_B @ sk_B_1) @ sk_A)),
% 0.20/0.53      inference('demod', [status(thm)], ['53', '54', '55', '56', '75'])).
% 0.20/0.53  thf('77', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ (u1_pre_topc @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['47', '76'])).
% 0.20/0.53  thf('78', plain,
% 0.20/0.53      ((r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.53        (u1_pre_topc @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['42', '77'])).
% 0.20/0.53  thf('79', plain,
% 0.20/0.53      (![X10 : $i]:
% 0.20/0.53         ((m1_subset_1 @ (u1_pre_topc @ X10) @ 
% 0.20/0.53           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.20/0.53          | ~ (l1_pre_topc @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.53  thf('80', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.53          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.20/0.53          | (m1_subset_1 @ X3 @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.53  thf('81', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X0)
% 0.20/0.53          | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.53          | ~ (r2_hidden @ X1 @ (u1_pre_topc @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['79', '80'])).
% 0.20/0.53  thf('82', plain,
% 0.20/0.53      (((m1_subset_1 @ 
% 0.20/0.53         (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['78', '81'])).
% 0.20/0.53  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('84', plain,
% 0.20/0.53      ((m1_subset_1 @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['82', '83'])).
% 0.20/0.53  thf('85', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['17', '30'])).
% 0.20/0.53  thf('86', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.53          | ~ (v3_pre_topc @ X6 @ X7)
% 0.20/0.53          | (r2_hidden @ X6 @ (u1_pre_topc @ X7))
% 0.20/0.53          | ~ (l1_pre_topc @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.20/0.53  thf('87', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | ~ (l1_pre_topc @ sk_B_1)
% 0.20/0.53          | (r2_hidden @ X0 @ (u1_pre_topc @ sk_B_1))
% 0.20/0.53          | ~ (v3_pre_topc @ X0 @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['85', '86'])).
% 0.20/0.53  thf('88', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('89', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | (r2_hidden @ X0 @ (u1_pre_topc @ sk_B_1))
% 0.20/0.53          | ~ (v3_pre_topc @ X0 @ sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['87', '88'])).
% 0.20/0.53  thf('90', plain,
% 0.20/0.53      ((~ (v3_pre_topc @ 
% 0.20/0.53           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ sk_B_1)
% 0.20/0.53        | (r2_hidden @ 
% 0.20/0.53           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.53           (u1_pre_topc @ sk_B_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['84', '89'])).
% 0.20/0.53  thf('91', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['17', '30'])).
% 0.20/0.53  thf('92', plain,
% 0.20/0.53      (![X25 : $i]:
% 0.20/0.53         (~ (r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ X25) @ (sk_B @ X25)) @ 
% 0.20/0.53             (u1_pre_topc @ X25))
% 0.20/0.53          | (v3_tdlat_3 @ X25)
% 0.20/0.53          | ~ (l1_pre_topc @ X25))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tdlat_3])).
% 0.20/0.53  thf('93', plain,
% 0.20/0.53      ((~ (r2_hidden @ 
% 0.20/0.53           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.53           (u1_pre_topc @ sk_B_1))
% 0.20/0.53        | ~ (l1_pre_topc @ sk_B_1)
% 0.20/0.53        | (v3_tdlat_3 @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['91', '92'])).
% 0.20/0.53  thf('94', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('95', plain,
% 0.20/0.53      ((~ (r2_hidden @ 
% 0.20/0.53           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.53           (u1_pre_topc @ sk_B_1))
% 0.20/0.53        | (v3_tdlat_3 @ sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['93', '94'])).
% 0.20/0.53  thf('96', plain, (~ (v3_tdlat_3 @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('97', plain,
% 0.20/0.53      (~ (r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.53          (u1_pre_topc @ sk_B_1))),
% 0.20/0.53      inference('clc', [status(thm)], ['95', '96'])).
% 0.20/0.53  thf('98', plain,
% 0.20/0.53      (~ (v3_pre_topc @ 
% 0.20/0.53          (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ sk_B_1)),
% 0.20/0.53      inference('clc', [status(thm)], ['90', '97'])).
% 0.20/0.53  thf('99', plain,
% 0.20/0.53      ((m1_subset_1 @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['82', '83'])).
% 0.20/0.53  thf('100', plain,
% 0.20/0.53      ((m1_subset_1 @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['82', '83'])).
% 0.20/0.53  thf('101', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['17', '30'])).
% 0.20/0.53  thf('102', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i, X21 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X19)
% 0.20/0.53          | ~ (m1_pre_topc @ X21 @ X19)
% 0.20/0.53          | (v3_pre_topc @ X18 @ X21)
% 0.20/0.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.53          | ~ (v3_pre_topc @ X18 @ X19)
% 0.20/0.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.53  thf('103', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.20/0.53          | ~ (v3_pre_topc @ X0 @ X1)
% 0.20/0.53          | (v3_pre_topc @ X0 @ sk_B_1)
% 0.20/0.53          | ~ (m1_pre_topc @ sk_B_1 @ X1)
% 0.20/0.53          | ~ (l1_pre_topc @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['101', '102'])).
% 0.20/0.53  thf('104', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X0)
% 0.20/0.53          | ~ (m1_pre_topc @ sk_B_1 @ X0)
% 0.20/0.53          | (v3_pre_topc @ 
% 0.20/0.53             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ sk_B_1)
% 0.20/0.53          | ~ (v3_pre_topc @ 
% 0.20/0.53               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ X0)
% 0.20/0.53          | ~ (m1_subset_1 @ 
% 0.20/0.53               (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.53               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['100', '103'])).
% 0.20/0.53  thf('105', plain,
% 0.20/0.53      ((~ (v3_pre_topc @ 
% 0.20/0.53           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ sk_A)
% 0.20/0.53        | (v3_pre_topc @ 
% 0.20/0.53           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ sk_B_1)
% 0.20/0.53        | ~ (m1_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['99', '104'])).
% 0.20/0.53  thf('106', plain,
% 0.20/0.53      ((m1_subset_1 @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['82', '83'])).
% 0.20/0.53  thf('107', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.53          | ~ (r2_hidden @ X6 @ (u1_pre_topc @ X7))
% 0.20/0.53          | (v3_pre_topc @ X6 @ X7)
% 0.20/0.53          | ~ (l1_pre_topc @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_pre_topc])).
% 0.20/0.53  thf('108', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | (v3_pre_topc @ 
% 0.20/0.53           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ sk_A)
% 0.20/0.53        | ~ (r2_hidden @ 
% 0.20/0.53             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.53             (u1_pre_topc @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['106', '107'])).
% 0.20/0.53  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('110', plain,
% 0.20/0.53      ((r2_hidden @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.53        (u1_pre_topc @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['42', '77'])).
% 0.20/0.53  thf('111', plain,
% 0.20/0.53      ((v3_pre_topc @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.53        sk_A)),
% 0.20/0.53      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.20/0.53  thf('112', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.20/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('114', plain,
% 0.20/0.53      ((v3_pre_topc @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.20/0.53        sk_B_1)),
% 0.20/0.53      inference('demod', [status(thm)], ['105', '111', '112', '113'])).
% 0.20/0.53  thf('115', plain, ($false), inference('demod', [status(thm)], ['98', '114'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
