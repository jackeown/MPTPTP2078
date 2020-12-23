%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rgpNfixZJz

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 988 expanded)
%              Number of leaves         :   37 ( 290 expanded)
%              Depth                    :   27
%              Number of atoms          : 1034 (10564 expanded)
%              Number of equality atoms :   17 ( 100 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ( ~ ( v1_zfmisc_1 @ sk_B_2 )
    | ~ ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_2 )
   <= ~ ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_2 )
    | ~ ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
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
    ! [X24: $i] :
      ( ~ ( v1_zfmisc_1 @ X24 )
      | ( X24
        = ( k6_domain_1 @ X24 @ ( sk_B_1 @ X24 ) ) )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('4',plain,(
    ! [X24: $i] :
      ( ~ ( v1_zfmisc_1 @ X24 )
      | ( m1_subset_1 @ ( sk_B_1 @ X24 ) @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
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
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( v1_zfmisc_1 @ sk_B_2 )
    | ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v1_zfmisc_1 @ sk_B_2 )
   <= ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    ! [X24: $i] :
      ( ~ ( v1_zfmisc_1 @ X24 )
      | ( m1_subset_1 @ ( sk_B_1 @ X24 ) @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B_1 @ X0 ) @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    r1_tarski @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_zfmisc_1 @ sk_B_2 )
    | ( r2_hidden @ ( sk_B_1 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_B_1 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r2_hidden @ ( sk_B_1 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['11','23'])).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( m1_subset_1 @ X7 @ X8 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('27',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( m1_subset_1 @ ( sk_B_1 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('29',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X29 ) @ X28 ) @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('30',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B_1 @ sk_B_2 ) ) @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( m1_subset_1 @ ( sk_B_1 @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('34',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('35',plain,
    ( ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B_1 @ sk_B_2 ) )
        = ( k1_tarski @ ( sk_B_1 @ sk_B_2 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('38',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( r2_hidden @ ( sk_B @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r2_hidden @ ( sk_B @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('42',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B_1 @ sk_B_2 ) )
      = ( k1_tarski @ ( sk_B_1 @ sk_B_2 ) ) )
   <= ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['35','42'])).

thf('44',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_tex_2 @ ( k1_tarski @ ( sk_B_1 @ sk_B_2 ) ) @ sk_A ) )
   <= ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['30','31','32','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v2_tex_2 @ ( k1_tarski @ ( sk_B_1 @ sk_B_2 ) ) @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( v2_tex_2 @ sk_B_2 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 )
      | ~ ( v1_zfmisc_1 @ sk_B_2 ) )
   <= ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['9','46'])).

thf('48',plain,
    ( ( v1_zfmisc_1 @ sk_B_2 )
   <= ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['10'])).

thf('49',plain,
    ( ( ( v2_tex_2 @ sk_B_2 @ sk_A )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v2_tex_2 @ sk_B_2 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( v2_tex_2 @ sk_B_2 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,
    ( ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference('sat_resolution*',[status(thm)],['2','53'])).

thf('55',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['1','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('57',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v2_tex_2 @ X26 @ X27 )
      | ( X26
        = ( u1_struct_0 @ ( sk_C_1 @ X26 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_2
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v2_tex_2 @ sk_B_2 @ sk_A )
   <= ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('62',plain,
    ( ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['10'])).

thf('63',plain,(
    v2_tex_2 @ sk_B_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','53','62'])).

thf('64',plain,(
    v2_tex_2 @ sk_B_2 @ sk_A ),
    inference(simpl_trail,[status(thm)],['61','63'])).

thf('65',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_2
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['58','59','60','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_B_2
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( sk_B_2
    = ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('70',plain,(
    ! [X18: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 )
      | ~ ( v7_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('71',plain,
    ( ( v1_zfmisc_1 @ sk_B_2 )
    | ~ ( v7_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ~ ( l1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v2_tex_2 @ X26 @ X27 )
      | ( m1_pre_topc @ ( sk_C_1 @ X26 @ X27 ) @ X27 )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_tex_2 @ sk_B_2 @ sk_A ),
    inference(simpl_trail,[status(thm)],['61','63'])).

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A ),
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
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ~ ( v1_tdlat_3 @ X22 )
      | ( v7_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_tdlat_3 @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc32_tex_2])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v2_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ),
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

thf('88',plain,
    ( ( v2_tex_2 @ sk_B_2 @ sk_A )
   <= ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('89',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v2_tex_2 @ X26 @ X27 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ X26 @ X27 ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('91',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['88','94'])).

thf('96',plain,(
    v2_tex_2 @ sk_B_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','53','62'])).

thf('97',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( v7_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['84','85','86','87','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v2_tex_2 @ X26 @ X27 )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ X26 @ X27 ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,(
    v2_tex_2 @ sk_B_2 @ sk_A ),
    inference(simpl_trail,[status(thm)],['61','63'])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    v7_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['104','116'])).

thf('118',plain,(
    m1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['80','81'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('119',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( l1_pre_topc @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('120',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    l1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['120','121'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('123',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('124',plain,(
    l1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(demod,[status(thm)],['71','117','124'])).

thf('126',plain,(
    $false ),
    inference(demod,[status(thm)],['55','125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rgpNfixZJz
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:50:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 158 iterations in 0.083s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.54  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.20/0.54  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.54  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.54  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.54  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.54  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.54  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.54  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.54  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.20/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.54  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.20/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.54  thf(t44_tex_2, conjecture,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.20/0.54         ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.54             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.54           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i]:
% 0.20/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.54            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54          ( ![B:$i]:
% 0.20/0.54            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.54                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.54              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.20/0.54  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B_2) | ~ (v2_tex_2 @ sk_B_2 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('1', plain, ((~ (v1_zfmisc_1 @ sk_B_2)) <= (~ ((v1_zfmisc_1 @ sk_B_2)))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (~ ((v1_zfmisc_1 @ sk_B_2)) | ~ ((v2_tex_2 @ sk_B_2 @ sk_A))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf(d1_tex_2, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.54       ( ( v1_zfmisc_1 @ A ) <=>
% 0.20/0.54         ( ?[B:$i]:
% 0.20/0.54           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X24 : $i]:
% 0.20/0.54         (~ (v1_zfmisc_1 @ X24)
% 0.20/0.54          | ((X24) = (k6_domain_1 @ X24 @ (sk_B_1 @ X24)))
% 0.20/0.54          | (v1_xboole_0 @ X24))),
% 0.20/0.54      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      (![X24 : $i]:
% 0.20/0.54         (~ (v1_zfmisc_1 @ X24)
% 0.20/0.54          | (m1_subset_1 @ (sk_B_1 @ X24) @ X24)
% 0.20/0.54          | (v1_xboole_0 @ X24))),
% 0.20/0.54      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.20/0.54  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.54       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X19 : $i, X20 : $i]:
% 0.20/0.54         ((v1_xboole_0 @ X19)
% 0.20/0.54          | ~ (m1_subset_1 @ X20 @ X19)
% 0.20/0.54          | ((k6_domain_1 @ X19 @ X20) = (k1_tarski @ X20)))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v1_xboole_0 @ X0)
% 0.20/0.54          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.54          | ((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.20/0.54          | (v1_xboole_0 @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.20/0.54          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.54          | (v1_xboole_0 @ X0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.54  thf('8', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((X0) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.20/0.54          | (v1_xboole_0 @ X0)
% 0.20/0.54          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.54          | (v1_xboole_0 @ X0)
% 0.20/0.54          | ~ (v1_zfmisc_1 @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['3', '7'])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (v1_zfmisc_1 @ X0)
% 0.20/0.54          | (v1_xboole_0 @ X0)
% 0.20/0.54          | ((X0) = (k1_tarski @ (sk_B_1 @ X0))))),
% 0.20/0.54      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.54  thf('10', plain, (((v1_zfmisc_1 @ sk_B_2) | (v2_tex_2 @ sk_B_2 @ sk_A))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('11', plain, (((v1_zfmisc_1 @ sk_B_2)) <= (((v1_zfmisc_1 @ sk_B_2)))),
% 0.20/0.54      inference('split', [status(esa)], ['10'])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (![X24 : $i]:
% 0.20/0.54         (~ (v1_zfmisc_1 @ X24)
% 0.20/0.54          | (m1_subset_1 @ (sk_B_1 @ X24) @ X24)
% 0.20/0.54          | (v1_xboole_0 @ X24))),
% 0.20/0.54      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.20/0.54  thf(d2_subset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.54       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.54  thf('13', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X7 @ X8)
% 0.20/0.54          | (r2_hidden @ X7 @ X8)
% 0.20/0.54          | (v1_xboole_0 @ X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v1_xboole_0 @ X0)
% 0.20/0.54          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.54          | (v1_xboole_0 @ X0)
% 0.20/0.54          | (r2_hidden @ (sk_B_1 @ X0) @ X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r2_hidden @ (sk_B_1 @ X0) @ X0)
% 0.20/0.54          | ~ (v1_zfmisc_1 @ X0)
% 0.20/0.54          | (v1_xboole_0 @ X0))),
% 0.20/0.54      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t3_subset, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X12 : $i, X13 : $i]:
% 0.20/0.54         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.20/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.54  thf('18', plain, ((r1_tarski @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.54  thf(d3_tarski, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.54          | (r2_hidden @ X3 @ X5)
% 0.20/0.54          | ~ (r1_tarski @ X4 @ X5))),
% 0.20/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.20/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (((v1_xboole_0 @ sk_B_2)
% 0.20/0.54        | ~ (v1_zfmisc_1 @ sk_B_2)
% 0.20/0.54        | (r2_hidden @ (sk_B_1 @ sk_B_2) @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['15', '20'])).
% 0.20/0.54  thf('22', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      (((r2_hidden @ (sk_B_1 @ sk_B_2) @ (u1_struct_0 @ sk_A))
% 0.20/0.54        | ~ (v1_zfmisc_1 @ sk_B_2))),
% 0.20/0.54      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (((r2_hidden @ (sk_B_1 @ sk_B_2) @ (u1_struct_0 @ sk_A)))
% 0.20/0.54         <= (((v1_zfmisc_1 @ sk_B_2)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['11', '23'])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X7 @ X8)
% 0.20/0.54          | (m1_subset_1 @ X7 @ X8)
% 0.20/0.54          | (v1_xboole_0 @ X8))),
% 0.20/0.54      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.54  thf(d1_xboole_0, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      (![X7 : $i, X8 : $i]: ((m1_subset_1 @ X7 @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 0.20/0.54      inference('clc', [status(thm)], ['25', '26'])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      (((m1_subset_1 @ (sk_B_1 @ sk_B_2) @ (u1_struct_0 @ sk_A)))
% 0.20/0.54         <= (((v1_zfmisc_1 @ sk_B_2)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['24', '27'])).
% 0.20/0.54  thf(t36_tex_2, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      (![X28 : $i, X29 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 0.20/0.54          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X29) @ X28) @ X29)
% 0.20/0.54          | ~ (l1_pre_topc @ X29)
% 0.20/0.54          | ~ (v2_pre_topc @ X29)
% 0.20/0.54          | (v2_struct_0 @ X29))),
% 0.20/0.54      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      ((((v2_struct_0 @ sk_A)
% 0.20/0.54         | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54         | (v2_tex_2 @ 
% 0.20/0.54            (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B_1 @ sk_B_2)) @ sk_A)))
% 0.20/0.54         <= (((v1_zfmisc_1 @ sk_B_2)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.54  thf('31', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      (((m1_subset_1 @ (sk_B_1 @ sk_B_2) @ (u1_struct_0 @ sk_A)))
% 0.20/0.54         <= (((v1_zfmisc_1 @ sk_B_2)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['24', '27'])).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      (![X19 : $i, X20 : $i]:
% 0.20/0.54         ((v1_xboole_0 @ X19)
% 0.20/0.54          | ~ (m1_subset_1 @ X20 @ X19)
% 0.20/0.54          | ((k6_domain_1 @ X19 @ X20) = (k1_tarski @ X20)))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      (((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B_1 @ sk_B_2))
% 0.20/0.54           = (k1_tarski @ (sk_B_1 @ sk_B_2)))
% 0.20/0.54         | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))) <= (((v1_zfmisc_1 @ sk_B_2)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.20/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      (((v1_xboole_0 @ sk_B_2)
% 0.20/0.54        | (r2_hidden @ (sk_B @ sk_B_2) @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.54  thf('39', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('40', plain, ((r2_hidden @ (sk_B @ sk_B_2) @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('clc', [status(thm)], ['38', '39'])).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.54  thf('42', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B_1 @ sk_B_2))
% 0.20/0.54          = (k1_tarski @ (sk_B_1 @ sk_B_2))))
% 0.20/0.54         <= (((v1_zfmisc_1 @ sk_B_2)))),
% 0.20/0.54      inference('clc', [status(thm)], ['35', '42'])).
% 0.20/0.54  thf('44', plain,
% 0.20/0.54      ((((v2_struct_0 @ sk_A)
% 0.20/0.54         | (v2_tex_2 @ (k1_tarski @ (sk_B_1 @ sk_B_2)) @ sk_A)))
% 0.20/0.54         <= (((v1_zfmisc_1 @ sk_B_2)))),
% 0.20/0.54      inference('demod', [status(thm)], ['30', '31', '32', '43'])).
% 0.20/0.54  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('46', plain,
% 0.20/0.54      (((v2_tex_2 @ (k1_tarski @ (sk_B_1 @ sk_B_2)) @ sk_A))
% 0.20/0.54         <= (((v1_zfmisc_1 @ sk_B_2)))),
% 0.20/0.54      inference('clc', [status(thm)], ['44', '45'])).
% 0.20/0.54  thf('47', plain,
% 0.20/0.54      ((((v2_tex_2 @ sk_B_2 @ sk_A)
% 0.20/0.54         | (v1_xboole_0 @ sk_B_2)
% 0.20/0.54         | ~ (v1_zfmisc_1 @ sk_B_2))) <= (((v1_zfmisc_1 @ sk_B_2)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['9', '46'])).
% 0.20/0.54  thf('48', plain, (((v1_zfmisc_1 @ sk_B_2)) <= (((v1_zfmisc_1 @ sk_B_2)))),
% 0.20/0.54      inference('split', [status(esa)], ['10'])).
% 0.20/0.54  thf('49', plain,
% 0.20/0.54      ((((v2_tex_2 @ sk_B_2 @ sk_A) | (v1_xboole_0 @ sk_B_2)))
% 0.20/0.54         <= (((v1_zfmisc_1 @ sk_B_2)))),
% 0.20/0.54      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.54  thf('50', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('51', plain,
% 0.20/0.54      (((v2_tex_2 @ sk_B_2 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_2)))),
% 0.20/0.54      inference('clc', [status(thm)], ['49', '50'])).
% 0.20/0.54  thf('52', plain,
% 0.20/0.54      ((~ (v2_tex_2 @ sk_B_2 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf('53', plain, (((v2_tex_2 @ sk_B_2 @ sk_A)) | ~ ((v1_zfmisc_1 @ sk_B_2))),
% 0.20/0.54      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.54  thf('54', plain, (~ ((v1_zfmisc_1 @ sk_B_2))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['2', '53'])).
% 0.20/0.54  thf('55', plain, (~ (v1_zfmisc_1 @ sk_B_2)),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['1', '54'])).
% 0.20/0.54  thf('56', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t34_tex_2, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.54             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.54           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.20/0.54                ( ![C:$i]:
% 0.20/0.54                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.20/0.54                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.54                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf('57', plain,
% 0.20/0.54      (![X26 : $i, X27 : $i]:
% 0.20/0.54         ((v1_xboole_0 @ X26)
% 0.20/0.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.20/0.54          | ~ (v2_tex_2 @ X26 @ X27)
% 0.20/0.54          | ((X26) = (u1_struct_0 @ (sk_C_1 @ X26 @ X27)))
% 0.20/0.54          | ~ (l1_pre_topc @ X27)
% 0.20/0.54          | ~ (v2_pre_topc @ X27)
% 0.20/0.54          | (v2_struct_0 @ X27))),
% 0.20/0.54      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.20/0.54  thf('58', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | ((sk_B_2) = (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)))
% 0.20/0.54        | ~ (v2_tex_2 @ sk_B_2 @ sk_A)
% 0.20/0.54        | (v1_xboole_0 @ sk_B_2))),
% 0.20/0.54      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.54  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('61', plain,
% 0.20/0.54      (((v2_tex_2 @ sk_B_2 @ sk_A)) <= (((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['10'])).
% 0.20/0.54  thf('62', plain, (((v2_tex_2 @ sk_B_2 @ sk_A)) | ((v1_zfmisc_1 @ sk_B_2))),
% 0.20/0.54      inference('split', [status(esa)], ['10'])).
% 0.20/0.54  thf('63', plain, (((v2_tex_2 @ sk_B_2 @ sk_A))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['2', '53', '62'])).
% 0.20/0.54  thf('64', plain, ((v2_tex_2 @ sk_B_2 @ sk_A)),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['61', '63'])).
% 0.20/0.54  thf('65', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | ((sk_B_2) = (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)))
% 0.20/0.54        | (v1_xboole_0 @ sk_B_2))),
% 0.20/0.54      inference('demod', [status(thm)], ['58', '59', '60', '64'])).
% 0.20/0.54  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('67', plain,
% 0.20/0.54      (((v1_xboole_0 @ sk_B_2)
% 0.20/0.54        | ((sk_B_2) = (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))))),
% 0.20/0.54      inference('clc', [status(thm)], ['65', '66'])).
% 0.20/0.54  thf('68', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('69', plain, (((sk_B_2) = (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)))),
% 0.20/0.54      inference('clc', [status(thm)], ['67', '68'])).
% 0.20/0.54  thf(fc7_struct_0, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.54       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.54  thf('70', plain,
% 0.20/0.54      (![X18 : $i]:
% 0.20/0.54         ((v1_zfmisc_1 @ (u1_struct_0 @ X18))
% 0.20/0.54          | ~ (l1_struct_0 @ X18)
% 0.20/0.54          | ~ (v7_struct_0 @ X18))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.20/0.54  thf('71', plain,
% 0.20/0.54      (((v1_zfmisc_1 @ sk_B_2)
% 0.20/0.54        | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.20/0.54        | ~ (l1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['69', '70'])).
% 0.20/0.54  thf('72', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('73', plain,
% 0.20/0.54      (![X26 : $i, X27 : $i]:
% 0.20/0.54         ((v1_xboole_0 @ X26)
% 0.20/0.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.20/0.54          | ~ (v2_tex_2 @ X26 @ X27)
% 0.20/0.54          | (m1_pre_topc @ (sk_C_1 @ X26 @ X27) @ X27)
% 0.20/0.54          | ~ (l1_pre_topc @ X27)
% 0.20/0.54          | ~ (v2_pre_topc @ X27)
% 0.20/0.54          | (v2_struct_0 @ X27))),
% 0.20/0.54      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.20/0.54  thf('74', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | (m1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A)
% 0.20/0.54        | ~ (v2_tex_2 @ sk_B_2 @ sk_A)
% 0.20/0.54        | (v1_xboole_0 @ sk_B_2))),
% 0.20/0.54      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.54  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('77', plain, ((v2_tex_2 @ sk_B_2 @ sk_A)),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['61', '63'])).
% 0.20/0.54  thf('78', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | (m1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A)
% 0.20/0.54        | (v1_xboole_0 @ sk_B_2))),
% 0.20/0.54      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 0.20/0.54  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('80', plain,
% 0.20/0.54      (((v1_xboole_0 @ sk_B_2)
% 0.20/0.54        | (m1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A))),
% 0.20/0.54      inference('clc', [status(thm)], ['78', '79'])).
% 0.20/0.54  thf('81', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('82', plain, ((m1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A)),
% 0.20/0.54      inference('clc', [status(thm)], ['80', '81'])).
% 0.20/0.54  thf(cc32_tex_2, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.20/0.54         ( l1_pre_topc @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.54           ( ( ( ~( v2_struct_0 @ B ) ) & ( ~( v7_struct_0 @ B ) ) ) =>
% 0.20/0.54             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tdlat_3 @ B ) ) ) ) ) ) ))).
% 0.20/0.54  thf('83', plain,
% 0.20/0.54      (![X22 : $i, X23 : $i]:
% 0.20/0.54         (~ (m1_pre_topc @ X22 @ X23)
% 0.20/0.54          | ~ (v1_tdlat_3 @ X22)
% 0.20/0.54          | (v7_struct_0 @ X22)
% 0.20/0.54          | (v2_struct_0 @ X22)
% 0.20/0.54          | ~ (l1_pre_topc @ X23)
% 0.20/0.54          | ~ (v2_tdlat_3 @ X23)
% 0.20/0.54          | ~ (v2_pre_topc @ X23)
% 0.20/0.54          | (v2_struct_0 @ X23))),
% 0.20/0.54      inference('cnf', [status(esa)], [cc32_tex_2])).
% 0.20/0.54  thf('84', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54        | ~ (v2_tdlat_3 @ sk_A)
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | (v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.20/0.54        | (v7_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.20/0.54        | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['82', '83'])).
% 0.20/0.54  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('86', plain, ((v2_tdlat_3 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('88', plain,
% 0.20/0.54      (((v2_tex_2 @ sk_B_2 @ sk_A)) <= (((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['10'])).
% 0.20/0.54  thf('89', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('90', plain,
% 0.20/0.54      (![X26 : $i, X27 : $i]:
% 0.20/0.54         ((v1_xboole_0 @ X26)
% 0.20/0.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.20/0.54          | ~ (v2_tex_2 @ X26 @ X27)
% 0.20/0.54          | (v1_tdlat_3 @ (sk_C_1 @ X26 @ X27))
% 0.20/0.54          | ~ (l1_pre_topc @ X27)
% 0.20/0.54          | ~ (v2_pre_topc @ X27)
% 0.20/0.54          | (v2_struct_0 @ X27))),
% 0.20/0.54      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.20/0.54  thf('91', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.54        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.54        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.20/0.54        | ~ (v2_tex_2 @ sk_B_2 @ sk_A)
% 0.20/0.54        | (v1_xboole_0 @ sk_B_2))),
% 0.20/0.54      inference('sup-', [status(thm)], ['89', '90'])).
% 0.20/0.54  thf('92', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('94', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.20/0.54        | ~ (v2_tex_2 @ sk_B_2 @ sk_A)
% 0.20/0.54        | (v1_xboole_0 @ sk_B_2))),
% 0.20/0.54      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.20/0.54  thf('95', plain,
% 0.20/0.54      ((((v1_xboole_0 @ sk_B_2)
% 0.20/0.54         | (v1_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.20/0.54         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['88', '94'])).
% 0.20/0.54  thf('96', plain, (((v2_tex_2 @ sk_B_2 @ sk_A))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['2', '53', '62'])).
% 0.20/0.54  thf('97', plain,
% 0.20/0.54      (((v1_xboole_0 @ sk_B_2)
% 0.20/0.54        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.20/0.54        | (v2_struct_0 @ sk_A))),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['95', '96'])).
% 0.20/0.54  thf('98', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('99', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A)))),
% 0.20/0.54      inference('clc', [status(thm)], ['97', '98'])).
% 0.20/0.54  thf('100', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('101', plain, ((v1_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A))),
% 0.20/0.54      inference('clc', [status(thm)], ['99', '100'])).
% 0.20/0.54  thf('102', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | (v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.20/0.54        | (v7_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['84', '85', '86', '87', '101'])).
% 0.20/0.54  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('104', plain,
% 0.20/0.54      (((v7_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.20/0.54        | (v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)))),
% 0.20/0.54      inference('clc', [status(thm)], ['102', '103'])).
% 0.20/0.54  thf('105', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('106', plain,
% 0.20/0.54      (![X26 : $i, X27 : $i]:
% 0.20/0.54         ((v1_xboole_0 @ X26)
% 0.20/0.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.20/0.54          | ~ (v2_tex_2 @ X26 @ X27)
% 0.20/0.54          | ~ (v2_struct_0 @ (sk_C_1 @ X26 @ X27))
% 0.20/0.54          | ~ (l1_pre_topc @ X27)
% 0.20/0.54          | ~ (v2_pre_topc @ X27)
% 0.20/0.54          | (v2_struct_0 @ X27))),
% 0.20/0.54      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.20/0.54  thf('107', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.55        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.20/0.55        | ~ (v2_tex_2 @ sk_B_2 @ sk_A)
% 0.20/0.55        | (v1_xboole_0 @ sk_B_2))),
% 0.20/0.55      inference('sup-', [status(thm)], ['105', '106'])).
% 0.20/0.55  thf('108', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('110', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_A)
% 0.20/0.55        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.20/0.55        | ~ (v2_tex_2 @ sk_B_2 @ sk_A)
% 0.20/0.55        | (v1_xboole_0 @ sk_B_2))),
% 0.20/0.55      inference('demod', [status(thm)], ['107', '108', '109'])).
% 0.20/0.55  thf('111', plain, ((v2_tex_2 @ sk_B_2 @ sk_A)),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['61', '63'])).
% 0.20/0.55  thf('112', plain,
% 0.20/0.55      (((v2_struct_0 @ sk_A)
% 0.20/0.55        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.20/0.55        | (v1_xboole_0 @ sk_B_2))),
% 0.20/0.55      inference('demod', [status(thm)], ['110', '111'])).
% 0.20/0.55  thf('113', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('114', plain,
% 0.20/0.55      (((v1_xboole_0 @ sk_B_2) | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)))),
% 0.20/0.55      inference('clc', [status(thm)], ['112', '113'])).
% 0.20/0.55  thf('115', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('116', plain, (~ (v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))),
% 0.20/0.55      inference('clc', [status(thm)], ['114', '115'])).
% 0.20/0.55  thf('117', plain, ((v7_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))),
% 0.20/0.55      inference('clc', [status(thm)], ['104', '116'])).
% 0.20/0.55  thf('118', plain, ((m1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A)),
% 0.20/0.55      inference('clc', [status(thm)], ['80', '81'])).
% 0.20/0.55  thf(dt_m1_pre_topc, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_pre_topc @ A ) =>
% 0.20/0.55       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.55  thf('119', plain,
% 0.20/0.55      (![X16 : $i, X17 : $i]:
% 0.20/0.55         (~ (m1_pre_topc @ X16 @ X17)
% 0.20/0.55          | (l1_pre_topc @ X16)
% 0.20/0.55          | ~ (l1_pre_topc @ X17))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.55  thf('120', plain,
% 0.20/0.55      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['118', '119'])).
% 0.20/0.55  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('122', plain, ((l1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['120', '121'])).
% 0.20/0.55  thf(dt_l1_pre_topc, axiom,
% 0.20/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.55  thf('123', plain,
% 0.20/0.55      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.55  thf('124', plain, ((l1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['122', '123'])).
% 0.20/0.55  thf('125', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 0.20/0.55      inference('demod', [status(thm)], ['71', '117', '124'])).
% 0.20/0.55  thf('126', plain, ($false), inference('demod', [status(thm)], ['55', '125'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
