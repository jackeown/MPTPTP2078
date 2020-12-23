%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uKzcKnPtYY

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:57 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  226 (2137 expanded)
%              Number of leaves         :   44 ( 635 expanded)
%              Depth                    :   31
%              Number of atoms          : 1501 (21161 expanded)
%              Number of equality atoms :   30 ( 210 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_tdlat_3_type,type,(
    v2_tdlat_3: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

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

thf('3',plain,
    ( ( v1_zfmisc_1 @ sk_B_2 )
    | ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v1_zfmisc_1 @ sk_B_2 )
   <= ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['3'])).

thf(rc1_subset_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ? [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( sk_B_1 @ X11 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[rc1_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_B_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf('8',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ~ ( v1_zfmisc_1 @ X33 )
      | ( X34 = X33 )
      | ~ ( r1_tarski @ X34 @ X33 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( ( sk_B_1 @ X0 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( ( sk_B_1 @ X0 )
        = X0 )
      | ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X11: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X11 ) )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[rc1_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( sk_B_1 @ X0 )
        = X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( ( sk_B_1 @ X0 )
        = X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_B_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( sk_B_1 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( sk_B_1 @ X0 ) ) @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X11: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B_1 @ X11 ) )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[rc1_subset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ ( sk_B_1 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    r1_tarski @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( r2_hidden @ ( sk_B @ ( sk_B_1 @ sk_B_2 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r2_hidden @ ( sk_B @ ( sk_B_1 @ sk_B_2 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('35',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( m1_subset_1 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ ( sk_B @ ( sk_B_1 @ sk_B_2 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','36'])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('38',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ X26 )
      | ( ( k6_domain_1 @ X26 @ X27 )
        = ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('39',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ ( sk_B_1 @ sk_B_2 ) ) )
      = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ sk_B_2 ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('41',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('42',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ ( sk_B_1 @ sk_B_2 ) ) )
    = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ sk_B_2 ) ) ) ),
    inference(clc,[status(thm)],['39','44'])).

thf('46',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_2 ) )
      = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ sk_B_2 ) ) ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['13','45'])).

thf('47',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( r2_hidden @ ( sk_B @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r2_hidden @ ( sk_B @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('53',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ X26 )
      | ( ( k6_domain_1 @ X26 @ X27 )
        = ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('55',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_2 ) )
      = ( k1_tarski @ ( sk_B @ sk_B_2 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('57',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_2 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k1_tarski @ ( sk_B @ sk_B_2 ) )
      = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ sk_B_2 ) ) ) )
    | ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['46','57'])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_2 )
    | ( ( k1_tarski @ ( sk_B @ sk_B_2 ) )
      = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ sk_B_2 ) ) ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k1_tarski @ ( sk_B @ sk_B_2 ) )
      = ( k1_tarski @ ( sk_B @ ( sk_B_1 @ sk_B_2 ) ) ) )
   <= ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['4','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ ( sk_B_1 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('63',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X12 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ ( sk_B_1 @ X0 ) ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ sk_B_2 ) ) @ ( k1_zfmisc_1 @ sk_B_2 ) )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ sk_B_2 ) ) @ ( k1_zfmisc_1 @ sk_B_2 ) )
   <= ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('69',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_B @ sk_B_2 ) ) @ sk_B_2 )
   <= ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ~ ( v1_zfmisc_1 @ X33 )
      | ( X34 = X33 )
      | ~ ( r1_tarski @ X34 @ X33 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t1_tex_2])).

thf('71',plain,
    ( ( ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_2 ) ) )
      | ( ( k1_tarski @ ( sk_B @ sk_B_2 ) )
        = sk_B_2 )
      | ~ ( v1_zfmisc_1 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( v1_zfmisc_1 @ sk_B_2 )
   <= ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['3'])).

thf('73',plain,
    ( ( ( v1_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_B_2 ) ) )
      | ( ( k1_tarski @ ( sk_B @ sk_B_2 ) )
        = sk_B_2 )
      | ( v1_xboole_0 @ sk_B_2 ) )
   <= ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('74',plain,(
    ! [X10: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('75',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( ( k1_tarski @ ( sk_B @ sk_B_2 ) )
        = sk_B_2 ) )
   <= ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( k1_tarski @ ( sk_B @ sk_B_2 ) )
      = sk_B_2 )
   <= ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ ( sk_B @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(t36_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) )).

thf('79',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X38 ) )
      | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ X38 ) @ X37 ) @ X38 )
      | ~ ( l1_pre_topc @ X38 )
      | ~ ( v2_pre_topc @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t36_tex_2])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_2 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_B_2 ) )
    = ( k1_tarski @ ( sk_B @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_2 ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['80','81','82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v2_tex_2 @ ( k1_tarski @ ( sk_B @ sk_B_2 ) ) @ sk_A ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( v2_tex_2 @ sk_B_2 @ sk_A )
   <= ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['77','86'])).

thf('88',plain,
    ( ~ ( v2_tex_2 @ sk_B_2 @ sk_A )
   <= ~ ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('89',plain,
    ( ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference('sat_resolution*',[status(thm)],['2','89'])).

thf('91',plain,(
    ~ ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['1','90'])).

thf('92',plain,(
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

thf('93',plain,(
    ! [X35: $i,X36: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v2_tex_2 @ X35 @ X36 )
      | ( X35
        = ( u1_struct_0 @ ( sk_C_1 @ X35 @ X36 ) ) )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('94',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B_2
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_2
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) )
    | ~ ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,
    ( ( v2_tex_2 @ sk_B_2 @ sk_A )
   <= ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('99',plain,
    ( ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_zfmisc_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['3'])).

thf('100',plain,(
    v2_tex_2 @ sk_B_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','89','99'])).

thf('101',plain,(
    v2_tex_2 @ sk_B_2 @ sk_A ),
    inference(simpl_trail,[status(thm)],['98','100'])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B_2
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['97','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_B_2
      = ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( sk_B_2
    = ( u1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['104','105'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('107',plain,(
    ! [X25: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ~ ( v7_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('108',plain,
    ( ( v1_zfmisc_1 @ sk_B_2 )
    | ~ ( v7_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ~ ( l1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( v2_tex_2 @ sk_B_2 @ sk_A )
   <= ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('110',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X35: $i,X36: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v2_tex_2 @ X35 @ X36 )
      | ( m1_pre_topc @ ( sk_C_1 @ X35 @ X36 ) @ X36 )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( m1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['109','115'])).

thf('117',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( m1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A )
   <= ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['118','119'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('121',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( l1_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('122',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( l1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( l1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['122','123'])).

thf(cc2_tex_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v1_tdlat_3 @ A )
          & ( v2_tdlat_3 @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v7_struct_0 @ A )
          & ( v2_pre_topc @ A ) ) ) ) )).

thf('125',plain,(
    ! [X30: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( v1_tdlat_3 @ X30 )
      | ~ ( v2_tdlat_3 @ X30 )
      | ( v7_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_1])).

thf('126',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
      | ~ ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
      | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( v2_tex_2 @ sk_B_2 @ sk_A )
   <= ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('128',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X35: $i,X36: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v2_tex_2 @ X35 @ X36 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ X35 @ X36 ) )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,
    ( ( ( v1_xboole_0 @ sk_B_2 )
      | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['127','133'])).

thf('135',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
      | ~ ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
      | ~ ( v2_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['126','138'])).

thf('140',plain,
    ( ( m1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) @ sk_A )
   <= ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['118','119'])).

thf(cc6_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v2_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_tdlat_3 @ B ) ) ) )).

thf('141',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X31 @ X32 )
      | ( v2_tdlat_3 @ X31 )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_tdlat_3 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[cc6_tdlat_3])).

thf('142',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( v2_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v2_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['142','143','144','145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( v2_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,(
    v2_tex_2 @ sk_B_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','89','99'])).

thf('150',plain,(
    v2_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( l1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['122','123'])).

thf(cc1_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_tdlat_3 @ A )
       => ( v2_pre_topc @ A ) ) ) )).

thf('152',plain,(
    ! [X28: $i] :
      ( ~ ( v1_tdlat_3 @ X28 )
      | ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc1_tdlat_3])).

thf('153',plain,
    ( ( ( v2_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
      | ~ ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( v1_tdlat_3 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('155',plain,
    ( ( v2_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,(
    v2_tex_2 @ sk_B_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','89','99'])).

thf('157',plain,(
    v2_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['155','156'])).

thf('158',plain,
    ( ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
      | ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) )
   <= ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['139','150','157'])).

thf('159',plain,(
    v2_tex_2 @ sk_B_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','89','99'])).

thf('160',plain,
    ( ( v7_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['158','159'])).

thf('161',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X35: $i,X36: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v2_tex_2 @ X35 @ X36 )
      | ~ ( v2_struct_0 @ ( sk_C_1 @ X35 @ X36 ) )
      | ~ ( l1_pre_topc @ X36 )
      | ~ ( v2_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t34_tex_2])).

thf('163',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B_2 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['163','164','165'])).

thf('167',plain,(
    v2_tex_2 @ sk_B_2 @ sk_A ),
    inference(simpl_trail,[status(thm)],['98','100'])).

thf('168',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['168','169'])).

thf('171',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    ~ ( v2_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['170','171'])).

thf('173',plain,(
    v7_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['160','172'])).

thf('174',plain,
    ( ( l1_pre_topc @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference(demod,[status(thm)],['122','123'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('175',plain,(
    ! [X22: $i] :
      ( ( l1_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('176',plain,
    ( ( l1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) )
   <= ( v2_tex_2 @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    v2_tex_2 @ sk_B_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','89','99'])).

thf('178',plain,(
    l1_struct_0 @ ( sk_C_1 @ sk_B_2 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['176','177'])).

thf('179',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(demod,[status(thm)],['108','173','178'])).

thf('180',plain,(
    $false ),
    inference(demod,[status(thm)],['91','179'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uKzcKnPtYY
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:04:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.48/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.48/0.69  % Solved by: fo/fo7.sh
% 0.48/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.69  % done 327 iterations in 0.235s
% 0.48/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.48/0.69  % SZS output start Refutation
% 0.48/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.48/0.69  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.48/0.69  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.48/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.69  thf(sk_B_type, type, sk_B: $i > $i).
% 0.48/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.69  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.48/0.69  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.48/0.69  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.48/0.69  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.48/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.48/0.69  thf(v2_tdlat_3_type, type, v2_tdlat_3: $i > $o).
% 0.48/0.69  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.48/0.69  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.48/0.69  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.48/0.69  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.48/0.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.48/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.69  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.48/0.69  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.48/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.69  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.48/0.69  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.48/0.69  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.48/0.69  thf(t44_tex_2, conjecture,
% 0.48/0.69    (![A:$i]:
% 0.48/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.48/0.69         ( l1_pre_topc @ A ) ) =>
% 0.48/0.69       ( ![B:$i]:
% 0.48/0.69         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.48/0.69             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.48/0.69           ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ))).
% 0.48/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.69    (~( ![A:$i]:
% 0.48/0.69        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.48/0.69            ( v2_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.69          ( ![B:$i]:
% 0.48/0.69            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.48/0.69                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.48/0.69              ( ( v2_tex_2 @ B @ A ) <=> ( v1_zfmisc_1 @ B ) ) ) ) ) )),
% 0.48/0.69    inference('cnf.neg', [status(esa)], [t44_tex_2])).
% 0.48/0.69  thf('0', plain, ((~ (v1_zfmisc_1 @ sk_B_2) | ~ (v2_tex_2 @ sk_B_2 @ sk_A))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('1', plain, ((~ (v1_zfmisc_1 @ sk_B_2)) <= (~ ((v1_zfmisc_1 @ sk_B_2)))),
% 0.48/0.69      inference('split', [status(esa)], ['0'])).
% 0.48/0.69  thf('2', plain,
% 0.48/0.69      (~ ((v1_zfmisc_1 @ sk_B_2)) | ~ ((v2_tex_2 @ sk_B_2 @ sk_A))),
% 0.48/0.69      inference('split', [status(esa)], ['0'])).
% 0.48/0.69  thf('3', plain, (((v1_zfmisc_1 @ sk_B_2) | (v2_tex_2 @ sk_B_2 @ sk_A))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('4', plain, (((v1_zfmisc_1 @ sk_B_2)) <= (((v1_zfmisc_1 @ sk_B_2)))),
% 0.48/0.69      inference('split', [status(esa)], ['3'])).
% 0.48/0.69  thf(rc1_subset_1, axiom,
% 0.48/0.69    (![A:$i]:
% 0.48/0.69     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.48/0.69       ( ?[B:$i]:
% 0.48/0.69         ( ( ~( v1_xboole_0 @ B ) ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ) ))).
% 0.48/0.69  thf('5', plain,
% 0.48/0.69      (![X11 : $i]:
% 0.48/0.69         ((m1_subset_1 @ (sk_B_1 @ X11) @ (k1_zfmisc_1 @ X11))
% 0.48/0.69          | (v1_xboole_0 @ X11))),
% 0.48/0.69      inference('cnf', [status(esa)], [rc1_subset_1])).
% 0.48/0.69  thf(t3_subset, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.48/0.69  thf('6', plain,
% 0.48/0.69      (![X16 : $i, X17 : $i]:
% 0.48/0.69         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.48/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.69  thf('7', plain,
% 0.48/0.69      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r1_tarski @ (sk_B_1 @ X0) @ X0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['5', '6'])).
% 0.48/0.69  thf(t1_tex_2, axiom,
% 0.48/0.69    (![A:$i]:
% 0.48/0.69     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.48/0.69       ( ![B:$i]:
% 0.48/0.69         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.48/0.69           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.48/0.69  thf('8', plain,
% 0.48/0.69      (![X33 : $i, X34 : $i]:
% 0.48/0.69         ((v1_xboole_0 @ X33)
% 0.48/0.69          | ~ (v1_zfmisc_1 @ X33)
% 0.48/0.69          | ((X34) = (X33))
% 0.48/0.69          | ~ (r1_tarski @ X34 @ X33)
% 0.48/0.69          | (v1_xboole_0 @ X34))),
% 0.48/0.69      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.48/0.69  thf('9', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((v1_xboole_0 @ X0)
% 0.48/0.69          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.48/0.69          | ((sk_B_1 @ X0) = (X0))
% 0.48/0.69          | ~ (v1_zfmisc_1 @ X0)
% 0.48/0.69          | (v1_xboole_0 @ X0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['7', '8'])).
% 0.48/0.69  thf('10', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         (~ (v1_zfmisc_1 @ X0)
% 0.48/0.69          | ((sk_B_1 @ X0) = (X0))
% 0.48/0.69          | (v1_xboole_0 @ (sk_B_1 @ X0))
% 0.48/0.69          | (v1_xboole_0 @ X0))),
% 0.48/0.69      inference('simplify', [status(thm)], ['9'])).
% 0.48/0.69  thf('11', plain,
% 0.48/0.69      (![X11 : $i]: (~ (v1_xboole_0 @ (sk_B_1 @ X11)) | (v1_xboole_0 @ X11))),
% 0.48/0.69      inference('cnf', [status(esa)], [rc1_subset_1])).
% 0.48/0.69  thf('12', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((v1_xboole_0 @ X0)
% 0.48/0.69          | ((sk_B_1 @ X0) = (X0))
% 0.48/0.69          | ~ (v1_zfmisc_1 @ X0)
% 0.48/0.69          | (v1_xboole_0 @ X0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['10', '11'])).
% 0.48/0.69  thf('13', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         (~ (v1_zfmisc_1 @ X0) | ((sk_B_1 @ X0) = (X0)) | (v1_xboole_0 @ X0))),
% 0.48/0.69      inference('simplify', [status(thm)], ['12'])).
% 0.48/0.69  thf(d1_xboole_0, axiom,
% 0.48/0.69    (![A:$i]:
% 0.48/0.69     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.48/0.69  thf('14', plain,
% 0.48/0.69      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.48/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.48/0.69  thf('15', plain,
% 0.48/0.69      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r1_tarski @ (sk_B_1 @ X0) @ X0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['5', '6'])).
% 0.48/0.69  thf(d3_tarski, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( r1_tarski @ A @ B ) <=>
% 0.48/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.48/0.69  thf('16', plain,
% 0.48/0.69      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.48/0.69         (~ (r2_hidden @ X3 @ X4)
% 0.48/0.69          | (r2_hidden @ X3 @ X5)
% 0.48/0.69          | ~ (r1_tarski @ X4 @ X5))),
% 0.48/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.69  thf('17', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         ((v1_xboole_0 @ X0)
% 0.48/0.69          | (r2_hidden @ X1 @ X0)
% 0.48/0.69          | ~ (r2_hidden @ X1 @ (sk_B_1 @ X0)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['15', '16'])).
% 0.48/0.69  thf('18', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((v1_xboole_0 @ (sk_B_1 @ X0))
% 0.48/0.69          | (r2_hidden @ (sk_B @ (sk_B_1 @ X0)) @ X0)
% 0.48/0.69          | (v1_xboole_0 @ X0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['14', '17'])).
% 0.48/0.69  thf('19', plain,
% 0.48/0.69      (![X11 : $i]: (~ (v1_xboole_0 @ (sk_B_1 @ X11)) | (v1_xboole_0 @ X11))),
% 0.48/0.69      inference('cnf', [status(esa)], [rc1_subset_1])).
% 0.48/0.69  thf('20', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ (sk_B_1 @ X0)) @ X0))),
% 0.48/0.69      inference('clc', [status(thm)], ['18', '19'])).
% 0.48/0.69  thf('21', plain,
% 0.48/0.69      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('22', plain,
% 0.48/0.69      (![X16 : $i, X17 : $i]:
% 0.48/0.69         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.48/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.69  thf('23', plain, ((r1_tarski @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.48/0.69      inference('sup-', [status(thm)], ['21', '22'])).
% 0.48/0.69  thf('24', plain,
% 0.48/0.69      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.48/0.69         (~ (r2_hidden @ X3 @ X4)
% 0.48/0.69          | (r2_hidden @ X3 @ X5)
% 0.48/0.69          | ~ (r1_tarski @ X4 @ X5))),
% 0.48/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.69  thf('25', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.48/0.69      inference('sup-', [status(thm)], ['23', '24'])).
% 0.48/0.69  thf('26', plain,
% 0.48/0.69      (((v1_xboole_0 @ sk_B_2)
% 0.48/0.69        | (r2_hidden @ (sk_B @ (sk_B_1 @ sk_B_2)) @ (u1_struct_0 @ sk_A)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['20', '25'])).
% 0.48/0.69  thf('27', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('28', plain,
% 0.48/0.69      ((r2_hidden @ (sk_B @ (sk_B_1 @ sk_B_2)) @ (u1_struct_0 @ sk_A))),
% 0.48/0.69      inference('clc', [status(thm)], ['26', '27'])).
% 0.48/0.69  thf('29', plain,
% 0.48/0.69      (![X4 : $i, X6 : $i]:
% 0.48/0.69         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.48/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.69  thf('30', plain,
% 0.48/0.69      (![X4 : $i, X6 : $i]:
% 0.48/0.69         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.48/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.48/0.69  thf('31', plain,
% 0.48/0.69      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['29', '30'])).
% 0.48/0.69  thf('32', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.48/0.69      inference('simplify', [status(thm)], ['31'])).
% 0.48/0.69  thf('33', plain,
% 0.48/0.69      (![X16 : $i, X18 : $i]:
% 0.48/0.69         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 0.48/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.69  thf('34', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['32', '33'])).
% 0.48/0.69  thf(t4_subset, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i]:
% 0.48/0.69     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.48/0.69       ( m1_subset_1 @ A @ C ) ))).
% 0.48/0.69  thf('35', plain,
% 0.48/0.69      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.48/0.69         (~ (r2_hidden @ X19 @ X20)
% 0.48/0.69          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.48/0.69          | (m1_subset_1 @ X19 @ X21))),
% 0.48/0.69      inference('cnf', [status(esa)], [t4_subset])).
% 0.48/0.69  thf('36', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['34', '35'])).
% 0.48/0.69  thf('37', plain,
% 0.48/0.69      ((m1_subset_1 @ (sk_B @ (sk_B_1 @ sk_B_2)) @ (u1_struct_0 @ sk_A))),
% 0.48/0.69      inference('sup-', [status(thm)], ['28', '36'])).
% 0.48/0.69  thf(redefinition_k6_domain_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.48/0.69       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.48/0.69  thf('38', plain,
% 0.48/0.69      (![X26 : $i, X27 : $i]:
% 0.48/0.69         ((v1_xboole_0 @ X26)
% 0.48/0.69          | ~ (m1_subset_1 @ X27 @ X26)
% 0.48/0.69          | ((k6_domain_1 @ X26 @ X27) = (k1_tarski @ X27)))),
% 0.48/0.69      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.48/0.69  thf('39', plain,
% 0.48/0.69      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ (sk_B_1 @ sk_B_2)))
% 0.48/0.69          = (k1_tarski @ (sk_B @ (sk_B_1 @ sk_B_2))))
% 0.48/0.69        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['37', '38'])).
% 0.48/0.69  thf('40', plain,
% 0.48/0.69      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf(cc1_subset_1, axiom,
% 0.48/0.69    (![A:$i]:
% 0.48/0.69     ( ( v1_xboole_0 @ A ) =>
% 0.48/0.69       ( ![B:$i]:
% 0.48/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.48/0.69  thf('41', plain,
% 0.48/0.69      (![X14 : $i, X15 : $i]:
% 0.48/0.69         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.48/0.69          | (v1_xboole_0 @ X14)
% 0.48/0.69          | ~ (v1_xboole_0 @ X15))),
% 0.48/0.69      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.48/0.69  thf('42', plain,
% 0.48/0.69      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_2))),
% 0.48/0.69      inference('sup-', [status(thm)], ['40', '41'])).
% 0.48/0.69  thf('43', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('44', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.48/0.69      inference('clc', [status(thm)], ['42', '43'])).
% 0.48/0.69  thf('45', plain,
% 0.48/0.69      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ (sk_B_1 @ sk_B_2)))
% 0.48/0.69         = (k1_tarski @ (sk_B @ (sk_B_1 @ sk_B_2))))),
% 0.48/0.69      inference('clc', [status(thm)], ['39', '44'])).
% 0.48/0.69  thf('46', plain,
% 0.48/0.69      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_2))
% 0.48/0.69          = (k1_tarski @ (sk_B @ (sk_B_1 @ sk_B_2))))
% 0.48/0.69        | (v1_xboole_0 @ sk_B_2)
% 0.48/0.69        | ~ (v1_zfmisc_1 @ sk_B_2))),
% 0.48/0.69      inference('sup+', [status(thm)], ['13', '45'])).
% 0.48/0.69  thf('47', plain,
% 0.48/0.69      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.48/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.48/0.69  thf('48', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.48/0.69      inference('sup-', [status(thm)], ['23', '24'])).
% 0.48/0.69  thf('49', plain,
% 0.48/0.69      (((v1_xboole_0 @ sk_B_2)
% 0.48/0.69        | (r2_hidden @ (sk_B @ sk_B_2) @ (u1_struct_0 @ sk_A)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['47', '48'])).
% 0.48/0.69  thf('50', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('51', plain, ((r2_hidden @ (sk_B @ sk_B_2) @ (u1_struct_0 @ sk_A))),
% 0.48/0.69      inference('clc', [status(thm)], ['49', '50'])).
% 0.48/0.69  thf('52', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['34', '35'])).
% 0.48/0.69  thf('53', plain, ((m1_subset_1 @ (sk_B @ sk_B_2) @ (u1_struct_0 @ sk_A))),
% 0.48/0.69      inference('sup-', [status(thm)], ['51', '52'])).
% 0.48/0.69  thf('54', plain,
% 0.48/0.69      (![X26 : $i, X27 : $i]:
% 0.48/0.69         ((v1_xboole_0 @ X26)
% 0.48/0.69          | ~ (m1_subset_1 @ X27 @ X26)
% 0.48/0.69          | ((k6_domain_1 @ X26 @ X27) = (k1_tarski @ X27)))),
% 0.48/0.69      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.48/0.69  thf('55', plain,
% 0.48/0.69      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_2))
% 0.48/0.69          = (k1_tarski @ (sk_B @ sk_B_2)))
% 0.48/0.69        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['53', '54'])).
% 0.48/0.69  thf('56', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.48/0.69      inference('clc', [status(thm)], ['42', '43'])).
% 0.48/0.69  thf('57', plain,
% 0.48/0.69      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_2))
% 0.48/0.69         = (k1_tarski @ (sk_B @ sk_B_2)))),
% 0.48/0.69      inference('clc', [status(thm)], ['55', '56'])).
% 0.48/0.69  thf('58', plain,
% 0.48/0.69      ((((k1_tarski @ (sk_B @ sk_B_2))
% 0.48/0.69          = (k1_tarski @ (sk_B @ (sk_B_1 @ sk_B_2))))
% 0.48/0.69        | (v1_xboole_0 @ sk_B_2)
% 0.48/0.69        | ~ (v1_zfmisc_1 @ sk_B_2))),
% 0.48/0.69      inference('demod', [status(thm)], ['46', '57'])).
% 0.48/0.69  thf('59', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('60', plain,
% 0.48/0.69      ((~ (v1_zfmisc_1 @ sk_B_2)
% 0.48/0.69        | ((k1_tarski @ (sk_B @ sk_B_2))
% 0.48/0.69            = (k1_tarski @ (sk_B @ (sk_B_1 @ sk_B_2)))))),
% 0.48/0.69      inference('clc', [status(thm)], ['58', '59'])).
% 0.48/0.69  thf('61', plain,
% 0.48/0.69      ((((k1_tarski @ (sk_B @ sk_B_2))
% 0.48/0.69          = (k1_tarski @ (sk_B @ (sk_B_1 @ sk_B_2)))))
% 0.48/0.69         <= (((v1_zfmisc_1 @ sk_B_2)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['4', '60'])).
% 0.48/0.69  thf('62', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ (sk_B_1 @ X0)) @ X0))),
% 0.48/0.69      inference('clc', [status(thm)], ['18', '19'])).
% 0.48/0.69  thf(t63_subset_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( r2_hidden @ A @ B ) =>
% 0.48/0.69       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.48/0.69  thf('63', plain,
% 0.48/0.69      (![X12 : $i, X13 : $i]:
% 0.48/0.69         ((m1_subset_1 @ (k1_tarski @ X12) @ (k1_zfmisc_1 @ X13))
% 0.48/0.69          | ~ (r2_hidden @ X12 @ X13))),
% 0.48/0.69      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.48/0.69  thf('64', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((v1_xboole_0 @ X0)
% 0.48/0.69          | (m1_subset_1 @ (k1_tarski @ (sk_B @ (sk_B_1 @ X0))) @ 
% 0.48/0.69             (k1_zfmisc_1 @ X0)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['62', '63'])).
% 0.48/0.69  thf('65', plain,
% 0.48/0.69      ((((m1_subset_1 @ (k1_tarski @ (sk_B @ sk_B_2)) @ (k1_zfmisc_1 @ sk_B_2))
% 0.48/0.69         | (v1_xboole_0 @ sk_B_2))) <= (((v1_zfmisc_1 @ sk_B_2)))),
% 0.48/0.69      inference('sup+', [status(thm)], ['61', '64'])).
% 0.48/0.69  thf('66', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('67', plain,
% 0.48/0.69      (((m1_subset_1 @ (k1_tarski @ (sk_B @ sk_B_2)) @ (k1_zfmisc_1 @ sk_B_2)))
% 0.48/0.69         <= (((v1_zfmisc_1 @ sk_B_2)))),
% 0.48/0.69      inference('clc', [status(thm)], ['65', '66'])).
% 0.48/0.69  thf('68', plain,
% 0.48/0.69      (![X16 : $i, X17 : $i]:
% 0.48/0.69         ((r1_tarski @ X16 @ X17) | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.48/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.69  thf('69', plain,
% 0.48/0.69      (((r1_tarski @ (k1_tarski @ (sk_B @ sk_B_2)) @ sk_B_2))
% 0.48/0.69         <= (((v1_zfmisc_1 @ sk_B_2)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['67', '68'])).
% 0.48/0.69  thf('70', plain,
% 0.48/0.69      (![X33 : $i, X34 : $i]:
% 0.48/0.69         ((v1_xboole_0 @ X33)
% 0.48/0.69          | ~ (v1_zfmisc_1 @ X33)
% 0.48/0.69          | ((X34) = (X33))
% 0.48/0.69          | ~ (r1_tarski @ X34 @ X33)
% 0.48/0.69          | (v1_xboole_0 @ X34))),
% 0.48/0.69      inference('cnf', [status(esa)], [t1_tex_2])).
% 0.48/0.69  thf('71', plain,
% 0.48/0.69      ((((v1_xboole_0 @ (k1_tarski @ (sk_B @ sk_B_2)))
% 0.48/0.69         | ((k1_tarski @ (sk_B @ sk_B_2)) = (sk_B_2))
% 0.48/0.69         | ~ (v1_zfmisc_1 @ sk_B_2)
% 0.48/0.69         | (v1_xboole_0 @ sk_B_2))) <= (((v1_zfmisc_1 @ sk_B_2)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['69', '70'])).
% 0.48/0.69  thf('72', plain, (((v1_zfmisc_1 @ sk_B_2)) <= (((v1_zfmisc_1 @ sk_B_2)))),
% 0.48/0.69      inference('split', [status(esa)], ['3'])).
% 0.48/0.69  thf('73', plain,
% 0.48/0.69      ((((v1_xboole_0 @ (k1_tarski @ (sk_B @ sk_B_2)))
% 0.48/0.69         | ((k1_tarski @ (sk_B @ sk_B_2)) = (sk_B_2))
% 0.48/0.69         | (v1_xboole_0 @ sk_B_2))) <= (((v1_zfmisc_1 @ sk_B_2)))),
% 0.48/0.69      inference('demod', [status(thm)], ['71', '72'])).
% 0.48/0.69  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.48/0.69  thf('74', plain, (![X10 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X10))),
% 0.48/0.69      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.48/0.69  thf('75', plain,
% 0.48/0.69      ((((v1_xboole_0 @ sk_B_2) | ((k1_tarski @ (sk_B @ sk_B_2)) = (sk_B_2))))
% 0.48/0.69         <= (((v1_zfmisc_1 @ sk_B_2)))),
% 0.48/0.69      inference('clc', [status(thm)], ['73', '74'])).
% 0.48/0.69  thf('76', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('77', plain,
% 0.48/0.69      ((((k1_tarski @ (sk_B @ sk_B_2)) = (sk_B_2)))
% 0.48/0.69         <= (((v1_zfmisc_1 @ sk_B_2)))),
% 0.48/0.69      inference('clc', [status(thm)], ['75', '76'])).
% 0.48/0.69  thf('78', plain, ((m1_subset_1 @ (sk_B @ sk_B_2) @ (u1_struct_0 @ sk_A))),
% 0.48/0.69      inference('sup-', [status(thm)], ['51', '52'])).
% 0.48/0.69  thf(t36_tex_2, axiom,
% 0.48/0.69    (![A:$i]:
% 0.48/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.69       ( ![B:$i]:
% 0.48/0.69         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.48/0.69           ( v2_tex_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ))).
% 0.48/0.69  thf('79', plain,
% 0.48/0.69      (![X37 : $i, X38 : $i]:
% 0.48/0.69         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X38))
% 0.48/0.69          | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ X38) @ X37) @ X38)
% 0.48/0.69          | ~ (l1_pre_topc @ X38)
% 0.48/0.69          | ~ (v2_pre_topc @ X38)
% 0.48/0.69          | (v2_struct_0 @ X38))),
% 0.48/0.69      inference('cnf', [status(esa)], [t36_tex_2])).
% 0.48/0.69  thf('80', plain,
% 0.48/0.69      (((v2_struct_0 @ sk_A)
% 0.48/0.69        | ~ (v2_pre_topc @ sk_A)
% 0.48/0.69        | ~ (l1_pre_topc @ sk_A)
% 0.48/0.69        | (v2_tex_2 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_2)) @ 
% 0.48/0.69           sk_A))),
% 0.48/0.69      inference('sup-', [status(thm)], ['78', '79'])).
% 0.48/0.69  thf('81', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('83', plain,
% 0.48/0.69      (((k6_domain_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_B_2))
% 0.48/0.69         = (k1_tarski @ (sk_B @ sk_B_2)))),
% 0.48/0.69      inference('clc', [status(thm)], ['55', '56'])).
% 0.48/0.69  thf('84', plain,
% 0.48/0.69      (((v2_struct_0 @ sk_A)
% 0.48/0.69        | (v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_2)) @ sk_A))),
% 0.48/0.69      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 0.48/0.69  thf('85', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('86', plain, ((v2_tex_2 @ (k1_tarski @ (sk_B @ sk_B_2)) @ sk_A)),
% 0.48/0.69      inference('clc', [status(thm)], ['84', '85'])).
% 0.48/0.69  thf('87', plain,
% 0.48/0.69      (((v2_tex_2 @ sk_B_2 @ sk_A)) <= (((v1_zfmisc_1 @ sk_B_2)))),
% 0.48/0.69      inference('sup+', [status(thm)], ['77', '86'])).
% 0.48/0.69  thf('88', plain,
% 0.48/0.69      ((~ (v2_tex_2 @ sk_B_2 @ sk_A)) <= (~ ((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('split', [status(esa)], ['0'])).
% 0.48/0.69  thf('89', plain, (((v2_tex_2 @ sk_B_2 @ sk_A)) | ~ ((v1_zfmisc_1 @ sk_B_2))),
% 0.48/0.69      inference('sup-', [status(thm)], ['87', '88'])).
% 0.48/0.69  thf('90', plain, (~ ((v1_zfmisc_1 @ sk_B_2))),
% 0.48/0.69      inference('sat_resolution*', [status(thm)], ['2', '89'])).
% 0.48/0.69  thf('91', plain, (~ (v1_zfmisc_1 @ sk_B_2)),
% 0.48/0.69      inference('simpl_trail', [status(thm)], ['1', '90'])).
% 0.48/0.69  thf('92', plain,
% 0.48/0.69      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf(t34_tex_2, axiom,
% 0.48/0.69    (![A:$i]:
% 0.48/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.69       ( ![B:$i]:
% 0.48/0.69         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.48/0.69             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.48/0.69           ( ~( ( v2_tex_2 @ B @ A ) & 
% 0.48/0.69                ( ![C:$i]:
% 0.48/0.69                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.48/0.69                      ( v1_tdlat_3 @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.48/0.69                    ( ( B ) != ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ))).
% 0.48/0.69  thf('93', plain,
% 0.48/0.69      (![X35 : $i, X36 : $i]:
% 0.48/0.69         ((v1_xboole_0 @ X35)
% 0.48/0.69          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.48/0.69          | ~ (v2_tex_2 @ X35 @ X36)
% 0.48/0.69          | ((X35) = (u1_struct_0 @ (sk_C_1 @ X35 @ X36)))
% 0.48/0.69          | ~ (l1_pre_topc @ X36)
% 0.48/0.69          | ~ (v2_pre_topc @ X36)
% 0.48/0.69          | (v2_struct_0 @ X36))),
% 0.48/0.69      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.48/0.69  thf('94', plain,
% 0.48/0.69      (((v2_struct_0 @ sk_A)
% 0.48/0.69        | ~ (v2_pre_topc @ sk_A)
% 0.48/0.69        | ~ (l1_pre_topc @ sk_A)
% 0.48/0.69        | ((sk_B_2) = (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)))
% 0.48/0.69        | ~ (v2_tex_2 @ sk_B_2 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_2))),
% 0.48/0.69      inference('sup-', [status(thm)], ['92', '93'])).
% 0.48/0.69  thf('95', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('97', plain,
% 0.48/0.69      (((v2_struct_0 @ sk_A)
% 0.48/0.69        | ((sk_B_2) = (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)))
% 0.48/0.69        | ~ (v2_tex_2 @ sk_B_2 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_2))),
% 0.48/0.69      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.48/0.69  thf('98', plain,
% 0.48/0.69      (((v2_tex_2 @ sk_B_2 @ sk_A)) <= (((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('split', [status(esa)], ['3'])).
% 0.48/0.69  thf('99', plain, (((v2_tex_2 @ sk_B_2 @ sk_A)) | ((v1_zfmisc_1 @ sk_B_2))),
% 0.48/0.69      inference('split', [status(esa)], ['3'])).
% 0.48/0.69  thf('100', plain, (((v2_tex_2 @ sk_B_2 @ sk_A))),
% 0.48/0.69      inference('sat_resolution*', [status(thm)], ['2', '89', '99'])).
% 0.48/0.69  thf('101', plain, ((v2_tex_2 @ sk_B_2 @ sk_A)),
% 0.48/0.69      inference('simpl_trail', [status(thm)], ['98', '100'])).
% 0.48/0.69  thf('102', plain,
% 0.48/0.69      (((v2_struct_0 @ sk_A)
% 0.48/0.69        | ((sk_B_2) = (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)))
% 0.48/0.69        | (v1_xboole_0 @ sk_B_2))),
% 0.48/0.69      inference('demod', [status(thm)], ['97', '101'])).
% 0.48/0.69  thf('103', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('104', plain,
% 0.48/0.69      (((v1_xboole_0 @ sk_B_2)
% 0.48/0.69        | ((sk_B_2) = (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))))),
% 0.48/0.69      inference('clc', [status(thm)], ['102', '103'])).
% 0.48/0.69  thf('105', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('106', plain, (((sk_B_2) = (u1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('clc', [status(thm)], ['104', '105'])).
% 0.48/0.69  thf(fc7_struct_0, axiom,
% 0.48/0.69    (![A:$i]:
% 0.48/0.69     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.48/0.69       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.48/0.69  thf('107', plain,
% 0.48/0.69      (![X25 : $i]:
% 0.48/0.69         ((v1_zfmisc_1 @ (u1_struct_0 @ X25))
% 0.48/0.69          | ~ (l1_struct_0 @ X25)
% 0.48/0.69          | ~ (v7_struct_0 @ X25))),
% 0.48/0.69      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.48/0.69  thf('108', plain,
% 0.48/0.69      (((v1_zfmisc_1 @ sk_B_2)
% 0.48/0.69        | ~ (v7_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.48/0.69        | ~ (l1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('sup+', [status(thm)], ['106', '107'])).
% 0.48/0.69  thf('109', plain,
% 0.48/0.69      (((v2_tex_2 @ sk_B_2 @ sk_A)) <= (((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('split', [status(esa)], ['3'])).
% 0.48/0.69  thf('110', plain,
% 0.48/0.69      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('111', plain,
% 0.48/0.69      (![X35 : $i, X36 : $i]:
% 0.48/0.69         ((v1_xboole_0 @ X35)
% 0.48/0.69          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.48/0.69          | ~ (v2_tex_2 @ X35 @ X36)
% 0.48/0.69          | (m1_pre_topc @ (sk_C_1 @ X35 @ X36) @ X36)
% 0.48/0.69          | ~ (l1_pre_topc @ X36)
% 0.48/0.69          | ~ (v2_pre_topc @ X36)
% 0.48/0.69          | (v2_struct_0 @ X36))),
% 0.48/0.69      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.48/0.69  thf('112', plain,
% 0.48/0.69      (((v2_struct_0 @ sk_A)
% 0.48/0.69        | ~ (v2_pre_topc @ sk_A)
% 0.48/0.69        | ~ (l1_pre_topc @ sk_A)
% 0.48/0.69        | (m1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A)
% 0.48/0.69        | ~ (v2_tex_2 @ sk_B_2 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_2))),
% 0.48/0.69      inference('sup-', [status(thm)], ['110', '111'])).
% 0.48/0.69  thf('113', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('115', plain,
% 0.48/0.69      (((v2_struct_0 @ sk_A)
% 0.48/0.69        | (m1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A)
% 0.48/0.69        | ~ (v2_tex_2 @ sk_B_2 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_2))),
% 0.48/0.69      inference('demod', [status(thm)], ['112', '113', '114'])).
% 0.48/0.69  thf('116', plain,
% 0.48/0.69      ((((v1_xboole_0 @ sk_B_2)
% 0.48/0.69         | (m1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A)
% 0.48/0.69         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['109', '115'])).
% 0.48/0.69  thf('117', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('118', plain,
% 0.48/0.69      ((((v2_struct_0 @ sk_A) | (m1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A)))
% 0.48/0.69         <= (((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('clc', [status(thm)], ['116', '117'])).
% 0.48/0.69  thf('119', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('120', plain,
% 0.48/0.69      (((m1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A))
% 0.48/0.69         <= (((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('clc', [status(thm)], ['118', '119'])).
% 0.48/0.69  thf(dt_m1_pre_topc, axiom,
% 0.48/0.69    (![A:$i]:
% 0.48/0.69     ( ( l1_pre_topc @ A ) =>
% 0.48/0.69       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.48/0.69  thf('121', plain,
% 0.48/0.69      (![X23 : $i, X24 : $i]:
% 0.48/0.69         (~ (m1_pre_topc @ X23 @ X24)
% 0.48/0.69          | (l1_pre_topc @ X23)
% 0.48/0.69          | ~ (l1_pre_topc @ X24))),
% 0.48/0.69      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.48/0.69  thf('122', plain,
% 0.48/0.69      (((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A))))
% 0.48/0.69         <= (((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['120', '121'])).
% 0.48/0.69  thf('123', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('124', plain,
% 0.48/0.69      (((l1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A)))
% 0.48/0.69         <= (((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('demod', [status(thm)], ['122', '123'])).
% 0.48/0.69  thf(cc2_tex_1, axiom,
% 0.48/0.69    (![A:$i]:
% 0.48/0.69     ( ( l1_pre_topc @ A ) =>
% 0.48/0.69       ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.48/0.69           ( v1_tdlat_3 @ A ) & ( v2_tdlat_3 @ A ) ) =>
% 0.48/0.69         ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( v2_pre_topc @ A ) ) ) ))).
% 0.48/0.69  thf('125', plain,
% 0.48/0.69      (![X30 : $i]:
% 0.48/0.69         ((v2_struct_0 @ X30)
% 0.48/0.69          | ~ (v2_pre_topc @ X30)
% 0.48/0.69          | ~ (v1_tdlat_3 @ X30)
% 0.48/0.69          | ~ (v2_tdlat_3 @ X30)
% 0.48/0.69          | (v7_struct_0 @ X30)
% 0.48/0.69          | ~ (l1_pre_topc @ X30))),
% 0.48/0.69      inference('cnf', [status(esa)], [cc2_tex_1])).
% 0.48/0.69  thf('126', plain,
% 0.48/0.69      ((((v7_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.48/0.69         | ~ (v2_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.48/0.69         | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.48/0.69         | ~ (v2_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.48/0.69         | (v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))))
% 0.48/0.69         <= (((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['124', '125'])).
% 0.48/0.69  thf('127', plain,
% 0.48/0.69      (((v2_tex_2 @ sk_B_2 @ sk_A)) <= (((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('split', [status(esa)], ['3'])).
% 0.48/0.69  thf('128', plain,
% 0.48/0.69      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('129', plain,
% 0.48/0.69      (![X35 : $i, X36 : $i]:
% 0.48/0.69         ((v1_xboole_0 @ X35)
% 0.48/0.69          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.48/0.69          | ~ (v2_tex_2 @ X35 @ X36)
% 0.48/0.69          | (v1_tdlat_3 @ (sk_C_1 @ X35 @ X36))
% 0.48/0.69          | ~ (l1_pre_topc @ X36)
% 0.48/0.69          | ~ (v2_pre_topc @ X36)
% 0.48/0.69          | (v2_struct_0 @ X36))),
% 0.48/0.69      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.48/0.69  thf('130', plain,
% 0.48/0.69      (((v2_struct_0 @ sk_A)
% 0.48/0.69        | ~ (v2_pre_topc @ sk_A)
% 0.48/0.69        | ~ (l1_pre_topc @ sk_A)
% 0.48/0.69        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.48/0.69        | ~ (v2_tex_2 @ sk_B_2 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_2))),
% 0.48/0.69      inference('sup-', [status(thm)], ['128', '129'])).
% 0.48/0.69  thf('131', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('132', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('133', plain,
% 0.48/0.69      (((v2_struct_0 @ sk_A)
% 0.48/0.69        | (v1_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.48/0.69        | ~ (v2_tex_2 @ sk_B_2 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_2))),
% 0.48/0.69      inference('demod', [status(thm)], ['130', '131', '132'])).
% 0.48/0.69  thf('134', plain,
% 0.48/0.69      ((((v1_xboole_0 @ sk_B_2)
% 0.48/0.69         | (v1_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.48/0.69         | (v2_struct_0 @ sk_A))) <= (((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['127', '133'])).
% 0.48/0.69  thf('135', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('136', plain,
% 0.48/0.69      ((((v2_struct_0 @ sk_A) | (v1_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A))))
% 0.48/0.69         <= (((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('clc', [status(thm)], ['134', '135'])).
% 0.48/0.69  thf('137', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('138', plain,
% 0.48/0.69      (((v1_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A)))
% 0.48/0.69         <= (((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('clc', [status(thm)], ['136', '137'])).
% 0.48/0.69  thf('139', plain,
% 0.48/0.69      ((((v7_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.48/0.69         | ~ (v2_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.48/0.69         | ~ (v2_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.48/0.69         | (v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))))
% 0.48/0.69         <= (((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('demod', [status(thm)], ['126', '138'])).
% 0.48/0.69  thf('140', plain,
% 0.48/0.69      (((m1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A) @ sk_A))
% 0.48/0.69         <= (((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('clc', [status(thm)], ['118', '119'])).
% 0.48/0.69  thf(cc6_tdlat_3, axiom,
% 0.48/0.69    (![A:$i]:
% 0.48/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v2_tdlat_3 @ A ) & 
% 0.48/0.69         ( l1_pre_topc @ A ) ) =>
% 0.48/0.69       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_tdlat_3 @ B ) ) ) ))).
% 0.48/0.69  thf('141', plain,
% 0.48/0.69      (![X31 : $i, X32 : $i]:
% 0.48/0.69         (~ (m1_pre_topc @ X31 @ X32)
% 0.48/0.69          | (v2_tdlat_3 @ X31)
% 0.48/0.69          | ~ (l1_pre_topc @ X32)
% 0.48/0.69          | ~ (v2_tdlat_3 @ X32)
% 0.48/0.69          | ~ (v2_pre_topc @ X32)
% 0.48/0.69          | (v2_struct_0 @ X32))),
% 0.48/0.69      inference('cnf', [status(esa)], [cc6_tdlat_3])).
% 0.48/0.69  thf('142', plain,
% 0.48/0.69      ((((v2_struct_0 @ sk_A)
% 0.48/0.69         | ~ (v2_pre_topc @ sk_A)
% 0.48/0.69         | ~ (v2_tdlat_3 @ sk_A)
% 0.48/0.69         | ~ (l1_pre_topc @ sk_A)
% 0.48/0.69         | (v2_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A))))
% 0.48/0.69         <= (((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['140', '141'])).
% 0.48/0.69  thf('143', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('144', plain, ((v2_tdlat_3 @ sk_A)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('145', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('146', plain,
% 0.48/0.69      ((((v2_struct_0 @ sk_A) | (v2_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A))))
% 0.48/0.69         <= (((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('demod', [status(thm)], ['142', '143', '144', '145'])).
% 0.48/0.69  thf('147', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('148', plain,
% 0.48/0.69      (((v2_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A)))
% 0.48/0.69         <= (((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('clc', [status(thm)], ['146', '147'])).
% 0.48/0.69  thf('149', plain, (((v2_tex_2 @ sk_B_2 @ sk_A))),
% 0.48/0.69      inference('sat_resolution*', [status(thm)], ['2', '89', '99'])).
% 0.48/0.69  thf('150', plain, ((v2_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A))),
% 0.48/0.69      inference('simpl_trail', [status(thm)], ['148', '149'])).
% 0.48/0.69  thf('151', plain,
% 0.48/0.69      (((l1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A)))
% 0.48/0.69         <= (((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('demod', [status(thm)], ['122', '123'])).
% 0.48/0.69  thf(cc1_tdlat_3, axiom,
% 0.48/0.69    (![A:$i]:
% 0.48/0.69     ( ( l1_pre_topc @ A ) => ( ( v1_tdlat_3 @ A ) => ( v2_pre_topc @ A ) ) ))).
% 0.48/0.69  thf('152', plain,
% 0.48/0.69      (![X28 : $i]:
% 0.48/0.69         (~ (v1_tdlat_3 @ X28) | (v2_pre_topc @ X28) | ~ (l1_pre_topc @ X28))),
% 0.48/0.69      inference('cnf', [status(esa)], [cc1_tdlat_3])).
% 0.48/0.69  thf('153', plain,
% 0.48/0.69      ((((v2_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.48/0.69         | ~ (v1_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A))))
% 0.48/0.69         <= (((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['151', '152'])).
% 0.48/0.69  thf('154', plain,
% 0.48/0.69      (((v1_tdlat_3 @ (sk_C_1 @ sk_B_2 @ sk_A)))
% 0.48/0.69         <= (((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('clc', [status(thm)], ['136', '137'])).
% 0.48/0.69  thf('155', plain,
% 0.48/0.69      (((v2_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A)))
% 0.48/0.69         <= (((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('demod', [status(thm)], ['153', '154'])).
% 0.48/0.69  thf('156', plain, (((v2_tex_2 @ sk_B_2 @ sk_A))),
% 0.48/0.69      inference('sat_resolution*', [status(thm)], ['2', '89', '99'])).
% 0.48/0.69  thf('157', plain, ((v2_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A))),
% 0.48/0.69      inference('simpl_trail', [status(thm)], ['155', '156'])).
% 0.48/0.69  thf('158', plain,
% 0.48/0.69      ((((v7_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.48/0.69         | (v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))))
% 0.48/0.69         <= (((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('demod', [status(thm)], ['139', '150', '157'])).
% 0.48/0.69  thf('159', plain, (((v2_tex_2 @ sk_B_2 @ sk_A))),
% 0.48/0.69      inference('sat_resolution*', [status(thm)], ['2', '89', '99'])).
% 0.48/0.69  thf('160', plain,
% 0.48/0.69      (((v7_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.48/0.69        | (v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('simpl_trail', [status(thm)], ['158', '159'])).
% 0.48/0.69  thf('161', plain,
% 0.48/0.69      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('162', plain,
% 0.48/0.69      (![X35 : $i, X36 : $i]:
% 0.48/0.69         ((v1_xboole_0 @ X35)
% 0.48/0.69          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.48/0.69          | ~ (v2_tex_2 @ X35 @ X36)
% 0.48/0.69          | ~ (v2_struct_0 @ (sk_C_1 @ X35 @ X36))
% 0.48/0.69          | ~ (l1_pre_topc @ X36)
% 0.48/0.69          | ~ (v2_pre_topc @ X36)
% 0.48/0.69          | (v2_struct_0 @ X36))),
% 0.48/0.69      inference('cnf', [status(esa)], [t34_tex_2])).
% 0.48/0.69  thf('163', plain,
% 0.48/0.69      (((v2_struct_0 @ sk_A)
% 0.48/0.69        | ~ (v2_pre_topc @ sk_A)
% 0.48/0.69        | ~ (l1_pre_topc @ sk_A)
% 0.48/0.69        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.48/0.69        | ~ (v2_tex_2 @ sk_B_2 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_2))),
% 0.48/0.69      inference('sup-', [status(thm)], ['161', '162'])).
% 0.48/0.69  thf('164', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('165', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('166', plain,
% 0.48/0.69      (((v2_struct_0 @ sk_A)
% 0.48/0.69        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.48/0.69        | ~ (v2_tex_2 @ sk_B_2 @ sk_A)
% 0.48/0.69        | (v1_xboole_0 @ sk_B_2))),
% 0.48/0.69      inference('demod', [status(thm)], ['163', '164', '165'])).
% 0.48/0.69  thf('167', plain, ((v2_tex_2 @ sk_B_2 @ sk_A)),
% 0.48/0.69      inference('simpl_trail', [status(thm)], ['98', '100'])).
% 0.48/0.69  thf('168', plain,
% 0.48/0.69      (((v2_struct_0 @ sk_A)
% 0.48/0.69        | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))
% 0.48/0.69        | (v1_xboole_0 @ sk_B_2))),
% 0.48/0.69      inference('demod', [status(thm)], ['166', '167'])).
% 0.48/0.69  thf('169', plain, (~ (v2_struct_0 @ sk_A)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('170', plain,
% 0.48/0.69      (((v1_xboole_0 @ sk_B_2) | ~ (v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('clc', [status(thm)], ['168', '169'])).
% 0.48/0.69  thf('171', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('172', plain, (~ (v2_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))),
% 0.48/0.69      inference('clc', [status(thm)], ['170', '171'])).
% 0.48/0.69  thf('173', plain, ((v7_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))),
% 0.48/0.69      inference('sup-', [status(thm)], ['160', '172'])).
% 0.48/0.69  thf('174', plain,
% 0.48/0.69      (((l1_pre_topc @ (sk_C_1 @ sk_B_2 @ sk_A)))
% 0.48/0.69         <= (((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('demod', [status(thm)], ['122', '123'])).
% 0.48/0.69  thf(dt_l1_pre_topc, axiom,
% 0.48/0.69    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.48/0.69  thf('175', plain,
% 0.48/0.69      (![X22 : $i]: ((l1_struct_0 @ X22) | ~ (l1_pre_topc @ X22))),
% 0.48/0.69      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.48/0.69  thf('176', plain,
% 0.48/0.69      (((l1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A)))
% 0.48/0.69         <= (((v2_tex_2 @ sk_B_2 @ sk_A)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['174', '175'])).
% 0.48/0.69  thf('177', plain, (((v2_tex_2 @ sk_B_2 @ sk_A))),
% 0.48/0.69      inference('sat_resolution*', [status(thm)], ['2', '89', '99'])).
% 0.48/0.69  thf('178', plain, ((l1_struct_0 @ (sk_C_1 @ sk_B_2 @ sk_A))),
% 0.48/0.69      inference('simpl_trail', [status(thm)], ['176', '177'])).
% 0.48/0.69  thf('179', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 0.48/0.69      inference('demod', [status(thm)], ['108', '173', '178'])).
% 0.48/0.69  thf('180', plain, ($false), inference('demod', [status(thm)], ['91', '179'])).
% 0.48/0.69  
% 0.48/0.69  % SZS output end Refutation
% 0.48/0.69  
% 0.48/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
