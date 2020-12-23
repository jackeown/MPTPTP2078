%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DeuwP8u1kL

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:08 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 705 expanded)
%              Number of leaves         :   33 ( 205 expanded)
%              Depth                    :   25
%              Number of atoms          : 1264 (8803 expanded)
%              Number of equality atoms :   17 (  42 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) )
        & ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('2',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X20 @ X21 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('9',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['11','12'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(cc2_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ~ ( v1_xboole_0 @ B )
           => ~ ( v1_subset_1 @ B @ A ) ) ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( v1_subset_1 @ X11 @ X12 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v1_zfmisc_1 @ X12 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_2])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ X7 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('22',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('23',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19 = X18 )
      | ( v1_subset_1 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13
       != ( k6_domain_1 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ X13 )
      | ( v1_zfmisc_1 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('29',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
       != ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
       != ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('33',plain,(
    ! [X5: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('34',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('36',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('37',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['25'])).

thf('42',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('43',plain,(
    ! [X18: $i,X19: $i] :
      ( ( X19 = X18 )
      | ( v1_subset_1 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('44',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['11','12'])).

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

thf('46',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( ( sk_C @ X15 @ X16 )
        = ( u1_struct_0 @ X15 ) )
      | ( v1_tex_2 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('47',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['25'])).

thf('51',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ~ ( v1_subset_1 @ ( sk_C @ X15 @ X16 ) @ ( u1_struct_0 @ X16 ) )
      | ( v1_tex_2 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('53',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['11','12'])).

thf('56',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['25'])).

thf('58',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['44','58'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('60',plain,(
    ! [X6: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 )
      | ~ ( v7_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('61',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ) )).

thf('63',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('64',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['11','12'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('70',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( l1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('71',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('75',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['61','68','75'])).

thf('77',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['77'])).

thf(t6_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
              & ( v1_zfmisc_1 @ A ) ) ) ) )).

thf('79',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ X25 )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ X25 @ X24 ) @ X25 )
      | ~ ( v1_zfmisc_1 @ X25 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t6_tex_2])).

thf('80',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['76','82'])).

thf('84',plain,(
    ! [X5: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('85',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['41','89'])).

thf('91',plain,(
    v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['40','90'])).

thf('92',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['77'])).

thf('93',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('94',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ~ ( v1_tex_2 @ X15 @ X16 )
      | ( X17
       != ( u1_struct_0 @ X15 ) )
      | ( v1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('95',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( v1_tex_2 @ X15 @ X16 )
      | ~ ( m1_pre_topc @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['93','95'])).

thf('97',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['11','12'])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['92','99'])).

thf('101',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['77'])).

thf('102',plain,(
    v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference('sat_resolution*',[status(thm)],['41','89','101'])).

thf('103',plain,(
    v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['100','102'])).

thf('104',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['19','91','103'])).

thf('105',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['92','99'])).

thf('106',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(cc4_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ~ ( v1_subset_1 @ B @ A ) ) ) )).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_subset_1 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc4_subset_1])).

thf('108',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['105','108'])).

thf('110',plain,(
    v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference('sat_resolution*',[status(thm)],['41','89','101'])).

thf('111',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['109','110'])).

thf('112',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['104','111'])).

thf('113',plain,(
    ! [X5: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('114',plain,
    ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('116',plain,(
    v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    $false ),
    inference(demod,[status(thm)],['6','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DeuwP8u1kL
% 0.15/0.36  % Computer   : n024.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 12:12:51 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 192 iterations in 0.100s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.38/0.57  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.38/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.57  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.38/0.57  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.57  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.38/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.57  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.38/0.57  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.38/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.57  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.38/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.57  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.38/0.57  thf(t20_tex_2, conjecture,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.57           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.38/0.57             ( v1_subset_1 @
% 0.38/0.57               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i]:
% 0.38/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.57          ( ![B:$i]:
% 0.38/0.57            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.57              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.38/0.57                ( v1_subset_1 @
% 0.38/0.57                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.38/0.57                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.38/0.57  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(dt_k1_tex_2, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.38/0.57         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.38/0.57         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.38/0.57         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      (![X20 : $i, X21 : $i]:
% 0.38/0.57         (~ (l1_pre_topc @ X20)
% 0.38/0.57          | (v2_struct_0 @ X20)
% 0.38/0.57          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.38/0.57          | ~ (v2_struct_0 @ (k1_tex_2 @ X20 @ X21)))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.38/0.57        | (v2_struct_0 @ sk_A)
% 0.38/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.57  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['2', '3'])).
% 0.38/0.57  thf('5', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('6', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.38/0.57      inference('clc', [status(thm)], ['4', '5'])).
% 0.38/0.57  thf('7', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('8', plain,
% 0.38/0.57      (![X20 : $i, X21 : $i]:
% 0.38/0.57         (~ (l1_pre_topc @ X20)
% 0.38/0.57          | (v2_struct_0 @ X20)
% 0.38/0.57          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.38/0.57          | (m1_pre_topc @ (k1_tex_2 @ X20 @ X21) @ X20))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.38/0.57  thf('9', plain,
% 0.38/0.57      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.38/0.57        | (v2_struct_0 @ sk_A)
% 0.38/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.57  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.38/0.57        | (v2_struct_0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.57  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('13', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.38/0.57      inference('clc', [status(thm)], ['11', '12'])).
% 0.38/0.57  thf(t1_tsep_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( l1_pre_topc @ A ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_pre_topc @ B @ A ) =>
% 0.38/0.57           ( m1_subset_1 @
% 0.38/0.57             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      (![X9 : $i, X10 : $i]:
% 0.38/0.57         (~ (m1_pre_topc @ X9 @ X10)
% 0.38/0.57          | (m1_subset_1 @ (u1_struct_0 @ X9) @ 
% 0.38/0.57             (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.38/0.57          | ~ (l1_pre_topc @ X10))),
% 0.38/0.57      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.38/0.57  thf('15', plain,
% 0.38/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.57        | (m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.57           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.57  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.57  thf(cc2_tex_2, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.57           ( ( ~( v1_xboole_0 @ B ) ) => ( ~( v1_subset_1 @ B @ A ) ) ) ) ) ))).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (![X11 : $i, X12 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.38/0.57          | ~ (v1_subset_1 @ X11 @ X12)
% 0.38/0.57          | (v1_xboole_0 @ X11)
% 0.38/0.57          | ~ (v1_zfmisc_1 @ X12)
% 0.38/0.57          | (v1_xboole_0 @ X12))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc2_tex_2])).
% 0.38/0.57  thf('19', plain,
% 0.38/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57        | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.38/0.57        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))
% 0.38/0.57        | ~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.57             (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.57  thf('20', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(dt_k6_domain_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.38/0.57       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.57  thf('21', plain,
% 0.38/0.57      (![X7 : $i, X8 : $i]:
% 0.38/0.57         ((v1_xboole_0 @ X7)
% 0.38/0.57          | ~ (m1_subset_1 @ X8 @ X7)
% 0.38/0.57          | (m1_subset_1 @ (k6_domain_1 @ X7 @ X8) @ (k1_zfmisc_1 @ X7)))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.38/0.57  thf('22', plain,
% 0.38/0.57      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.57         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.57        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.57  thf(d7_subset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.57       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.38/0.57  thf('23', plain,
% 0.38/0.57      (![X18 : $i, X19 : $i]:
% 0.38/0.57         (((X19) = (X18))
% 0.38/0.57          | (v1_subset_1 @ X19 @ X18)
% 0.38/0.57          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.38/0.57  thf('24', plain,
% 0.38/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.57           (u1_struct_0 @ sk_A))
% 0.38/0.57        | ((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.57           (u1_struct_0 @ sk_A))
% 0.38/0.57        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('26', plain,
% 0.38/0.57      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.57           (u1_struct_0 @ sk_A)))
% 0.38/0.57         <= (~
% 0.38/0.57             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.57               (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('split', [status(esa)], ['25'])).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      (((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.38/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.38/0.57         <= (~
% 0.38/0.57             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.57               (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['24', '26'])).
% 0.38/0.57  thf(d1_tex_2, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.57       ( ( v1_zfmisc_1 @ A ) <=>
% 0.38/0.57         ( ?[B:$i]:
% 0.38/0.57           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.38/0.57  thf('28', plain,
% 0.38/0.57      (![X13 : $i, X14 : $i]:
% 0.38/0.57         (((X13) != (k6_domain_1 @ X13 @ X14))
% 0.38/0.57          | ~ (m1_subset_1 @ X14 @ X13)
% 0.38/0.57          | (v1_zfmisc_1 @ X13)
% 0.38/0.57          | (v1_xboole_0 @ X13))),
% 0.38/0.57      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.38/0.57  thf('29', plain,
% 0.38/0.57      (((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.38/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.38/0.57         <= (~
% 0.38/0.57             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.57               (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.38/0.57  thf('30', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('31', plain,
% 0.38/0.57      (((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.38/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.38/0.57         <= (~
% 0.38/0.57             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.57               (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.38/0.57  thf('32', plain,
% 0.38/0.57      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.38/0.57         <= (~
% 0.38/0.57             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.57               (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('simplify', [status(thm)], ['31'])).
% 0.38/0.57  thf(fc2_struct_0, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.38/0.57       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.38/0.57  thf('33', plain,
% 0.38/0.57      (![X5 : $i]:
% 0.38/0.57         (~ (v1_xboole_0 @ (u1_struct_0 @ X5))
% 0.38/0.57          | ~ (l1_struct_0 @ X5)
% 0.38/0.57          | (v2_struct_0 @ X5))),
% 0.38/0.57      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.38/0.57  thf('34', plain,
% 0.38/0.57      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | (v2_struct_0 @ sk_A)
% 0.38/0.57         | ~ (l1_struct_0 @ sk_A)))
% 0.38/0.57         <= (~
% 0.38/0.57             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.57               (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.38/0.57  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(dt_l1_pre_topc, axiom,
% 0.38/0.57    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.38/0.57  thf('36', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.57  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.38/0.57  thf('38', plain,
% 0.38/0.57      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.38/0.57         <= (~
% 0.38/0.57             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.57               (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['34', '37'])).
% 0.38/0.57  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('40', plain,
% 0.38/0.57      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.57         <= (~
% 0.38/0.57             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.57               (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('clc', [status(thm)], ['38', '39'])).
% 0.38/0.57  thf('41', plain,
% 0.38/0.57      (~
% 0.38/0.57       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.57         (u1_struct_0 @ sk_A))) | 
% 0.38/0.57       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.38/0.57      inference('split', [status(esa)], ['25'])).
% 0.38/0.57  thf('42', plain,
% 0.38/0.57      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.57  thf('43', plain,
% 0.38/0.57      (![X18 : $i, X19 : $i]:
% 0.38/0.57         (((X19) = (X18))
% 0.38/0.57          | (v1_subset_1 @ X19 @ X18)
% 0.38/0.57          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.38/0.57      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.38/0.57  thf('44', plain,
% 0.38/0.57      (((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.57         (u1_struct_0 @ sk_A))
% 0.38/0.57        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.38/0.57  thf('45', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.38/0.57      inference('clc', [status(thm)], ['11', '12'])).
% 0.38/0.57  thf(d3_tex_2, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( l1_pre_topc @ A ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_pre_topc @ B @ A ) =>
% 0.38/0.57           ( ( v1_tex_2 @ B @ A ) <=>
% 0.38/0.57             ( ![C:$i]:
% 0.38/0.57               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.38/0.57                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.38/0.57  thf('46', plain,
% 0.38/0.57      (![X15 : $i, X16 : $i]:
% 0.38/0.57         (~ (m1_pre_topc @ X15 @ X16)
% 0.38/0.57          | ((sk_C @ X15 @ X16) = (u1_struct_0 @ X15))
% 0.38/0.57          | (v1_tex_2 @ X15 @ X16)
% 0.38/0.57          | ~ (l1_pre_topc @ X16))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.38/0.57  thf('47', plain,
% 0.38/0.57      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.57        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.38/0.57        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.38/0.57            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['45', '46'])).
% 0.38/0.57  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('49', plain,
% 0.38/0.57      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.38/0.57        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.38/0.57            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.38/0.57      inference('demod', [status(thm)], ['47', '48'])).
% 0.38/0.57  thf('50', plain,
% 0.38/0.57      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.38/0.57         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.57      inference('split', [status(esa)], ['25'])).
% 0.38/0.57  thf('51', plain,
% 0.38/0.57      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.38/0.57          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.38/0.57         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['49', '50'])).
% 0.38/0.57  thf('52', plain,
% 0.38/0.57      (![X15 : $i, X16 : $i]:
% 0.38/0.57         (~ (m1_pre_topc @ X15 @ X16)
% 0.38/0.57          | ~ (v1_subset_1 @ (sk_C @ X15 @ X16) @ (u1_struct_0 @ X16))
% 0.38/0.57          | (v1_tex_2 @ X15 @ X16)
% 0.38/0.57          | ~ (l1_pre_topc @ X16))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.38/0.57  thf('53', plain,
% 0.38/0.57      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.57            (u1_struct_0 @ sk_A))
% 0.38/0.57         | ~ (l1_pre_topc @ sk_A)
% 0.38/0.57         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.38/0.57         | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))
% 0.38/0.57         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['51', '52'])).
% 0.38/0.57  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('55', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.38/0.57      inference('clc', [status(thm)], ['11', '12'])).
% 0.38/0.57  thf('56', plain,
% 0.38/0.57      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.57            (u1_struct_0 @ sk_A))
% 0.38/0.57         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))
% 0.38/0.57         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.38/0.57  thf('57', plain,
% 0.38/0.57      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.38/0.57         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.57      inference('split', [status(esa)], ['25'])).
% 0.38/0.57  thf('58', plain,
% 0.38/0.57      ((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.57           (u1_struct_0 @ sk_A)))
% 0.38/0.57         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.57      inference('clc', [status(thm)], ['56', '57'])).
% 0.38/0.57  thf('59', plain,
% 0.38/0.57      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))
% 0.38/0.57         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['44', '58'])).
% 0.38/0.57  thf(fc7_struct_0, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.38/0.57       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.38/0.57  thf('60', plain,
% 0.38/0.57      (![X6 : $i]:
% 0.38/0.57         ((v1_zfmisc_1 @ (u1_struct_0 @ X6))
% 0.38/0.57          | ~ (l1_struct_0 @ X6)
% 0.38/0.57          | ~ (v7_struct_0 @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.38/0.57  thf('61', plain,
% 0.38/0.57      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.38/0.57         | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.38/0.57         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['59', '60'])).
% 0.38/0.57  thf('62', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(fc2_tex_2, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.38/0.57         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.57       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.38/0.57         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.38/0.57         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.38/0.57  thf('63', plain,
% 0.38/0.57      (![X22 : $i, X23 : $i]:
% 0.38/0.57         (~ (l1_pre_topc @ X22)
% 0.38/0.57          | (v2_struct_0 @ X22)
% 0.38/0.57          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.38/0.57          | (v7_struct_0 @ (k1_tex_2 @ X22 @ X23)))),
% 0.38/0.57      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.38/0.57  thf('64', plain,
% 0.38/0.57      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.38/0.57        | (v2_struct_0 @ sk_A)
% 0.38/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['62', '63'])).
% 0.38/0.57  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('66', plain,
% 0.38/0.57      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['64', '65'])).
% 0.38/0.57  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('68', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.38/0.57      inference('clc', [status(thm)], ['66', '67'])).
% 0.38/0.57  thf('69', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.38/0.57      inference('clc', [status(thm)], ['11', '12'])).
% 0.38/0.57  thf(dt_m1_pre_topc, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( l1_pre_topc @ A ) =>
% 0.38/0.57       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.38/0.57  thf('70', plain,
% 0.38/0.57      (![X3 : $i, X4 : $i]:
% 0.38/0.57         (~ (m1_pre_topc @ X3 @ X4) | (l1_pre_topc @ X3) | ~ (l1_pre_topc @ X4))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.38/0.57  thf('71', plain,
% 0.38/0.57      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['69', '70'])).
% 0.38/0.57  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('73', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.38/0.57      inference('demod', [status(thm)], ['71', '72'])).
% 0.38/0.57  thf('74', plain, (![X2 : $i]: ((l1_struct_0 @ X2) | ~ (l1_pre_topc @ X2))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.57  thf('75', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['73', '74'])).
% 0.38/0.57  thf('76', plain,
% 0.38/0.57      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.57         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['61', '68', '75'])).
% 0.38/0.57  thf('77', plain,
% 0.38/0.57      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.57         (u1_struct_0 @ sk_A))
% 0.38/0.57        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('78', plain,
% 0.38/0.57      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.57         (u1_struct_0 @ sk_A)))
% 0.38/0.57         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.57               (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('split', [status(esa)], ['77'])).
% 0.38/0.57  thf(t6_tex_2, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ A ) =>
% 0.38/0.57           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.38/0.57                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.38/0.57  thf('79', plain,
% 0.38/0.57      (![X24 : $i, X25 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X24 @ X25)
% 0.38/0.57          | ~ (v1_subset_1 @ (k6_domain_1 @ X25 @ X24) @ X25)
% 0.38/0.57          | ~ (v1_zfmisc_1 @ X25)
% 0.38/0.57          | (v1_xboole_0 @ X25))),
% 0.38/0.57      inference('cnf', [status(esa)], [t6_tex_2])).
% 0.38/0.57  thf('80', plain,
% 0.38/0.57      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.38/0.57         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.57               (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['78', '79'])).
% 0.38/0.57  thf('81', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('82', plain,
% 0.38/0.57      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57         | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.38/0.57         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.57               (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['80', '81'])).
% 0.38/0.57  thf('83', plain,
% 0.38/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.38/0.57         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) & 
% 0.38/0.57             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.57               (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['76', '82'])).
% 0.38/0.57  thf('84', plain,
% 0.38/0.57      (![X5 : $i]:
% 0.38/0.57         (~ (v1_xboole_0 @ (u1_struct_0 @ X5))
% 0.38/0.57          | ~ (l1_struct_0 @ X5)
% 0.38/0.57          | (v2_struct_0 @ X5))),
% 0.38/0.57      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.38/0.57  thf('85', plain,
% 0.38/0.57      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.38/0.57         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) & 
% 0.38/0.57             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.57               (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['83', '84'])).
% 0.38/0.57  thf('86', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.38/0.57  thf('87', plain,
% 0.38/0.57      (((v2_struct_0 @ sk_A))
% 0.38/0.57         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) & 
% 0.38/0.57             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.57               (u1_struct_0 @ sk_A))))),
% 0.38/0.57      inference('demod', [status(thm)], ['85', '86'])).
% 0.38/0.57  thf('88', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('89', plain,
% 0.38/0.57      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) | 
% 0.38/0.57       ~
% 0.38/0.57       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.57         (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['87', '88'])).
% 0.38/0.57  thf('90', plain,
% 0.38/0.57      (~
% 0.38/0.57       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.57         (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('sat_resolution*', [status(thm)], ['41', '89'])).
% 0.38/0.57  thf('91', plain, ((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['40', '90'])).
% 0.38/0.57  thf('92', plain,
% 0.38/0.57      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.38/0.57         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.57      inference('split', [status(esa)], ['77'])).
% 0.38/0.57  thf('93', plain,
% 0.38/0.57      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.57  thf('94', plain,
% 0.38/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.38/0.57         (~ (m1_pre_topc @ X15 @ X16)
% 0.38/0.57          | ~ (v1_tex_2 @ X15 @ X16)
% 0.38/0.57          | ((X17) != (u1_struct_0 @ X15))
% 0.38/0.57          | (v1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 0.38/0.57          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.38/0.57          | ~ (l1_pre_topc @ X16))),
% 0.38/0.57      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.38/0.57  thf('95', plain,
% 0.38/0.57      (![X15 : $i, X16 : $i]:
% 0.38/0.57         (~ (l1_pre_topc @ X16)
% 0.38/0.57          | ~ (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.38/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.38/0.57          | (v1_subset_1 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X16))
% 0.38/0.57          | ~ (v1_tex_2 @ X15 @ X16)
% 0.38/0.57          | ~ (m1_pre_topc @ X15 @ X16))),
% 0.38/0.57      inference('simplify', [status(thm)], ['94'])).
% 0.38/0.57  thf('96', plain,
% 0.38/0.57      ((~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.38/0.57        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.38/0.57        | (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.57           (u1_struct_0 @ sk_A))
% 0.38/0.57        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.57      inference('sup-', [status(thm)], ['93', '95'])).
% 0.38/0.57  thf('97', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.38/0.57      inference('clc', [status(thm)], ['11', '12'])).
% 0.38/0.57  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('99', plain,
% 0.38/0.57      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.38/0.57        | (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.57           (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.38/0.57  thf('100', plain,
% 0.38/0.57      (((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.57         (u1_struct_0 @ sk_A)))
% 0.38/0.57         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['92', '99'])).
% 0.38/0.57  thf('101', plain,
% 0.38/0.57      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) | 
% 0.38/0.57       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.57         (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('split', [status(esa)], ['77'])).
% 0.38/0.57  thf('102', plain, (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.38/0.57      inference('sat_resolution*', [status(thm)], ['41', '89', '101'])).
% 0.38/0.57  thf('103', plain,
% 0.38/0.57      ((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.57        (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['100', '102'])).
% 0.38/0.57  thf('104', plain,
% 0.38/0.57      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.38/0.57      inference('demod', [status(thm)], ['19', '91', '103'])).
% 0.38/0.57  thf('105', plain,
% 0.38/0.57      (((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.57         (u1_struct_0 @ sk_A)))
% 0.38/0.57         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['92', '99'])).
% 0.38/0.57  thf('106', plain,
% 0.38/0.57      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.57        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.57  thf(cc4_subset_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( v1_xboole_0 @ A ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.57           ( ~( v1_subset_1 @ B @ A ) ) ) ) ))).
% 0.38/0.57  thf('107', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.38/0.57          | ~ (v1_subset_1 @ X0 @ X1)
% 0.38/0.57          | ~ (v1_xboole_0 @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc4_subset_1])).
% 0.38/0.57  thf('108', plain,
% 0.38/0.57      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.57        | ~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.57             (u1_struct_0 @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['106', '107'])).
% 0.38/0.57  thf('109', plain,
% 0.38/0.57      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.38/0.57         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['105', '108'])).
% 0.38/0.57  thf('110', plain, (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.38/0.57      inference('sat_resolution*', [status(thm)], ['41', '89', '101'])).
% 0.38/0.57  thf('111', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['109', '110'])).
% 0.38/0.57  thf('112', plain,
% 0.38/0.57      ((v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.38/0.57      inference('clc', [status(thm)], ['104', '111'])).
% 0.38/0.57  thf('113', plain,
% 0.38/0.57      (![X5 : $i]:
% 0.38/0.57         (~ (v1_xboole_0 @ (u1_struct_0 @ X5))
% 0.38/0.57          | ~ (l1_struct_0 @ X5)
% 0.38/0.57          | (v2_struct_0 @ X5))),
% 0.38/0.57      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.38/0.57  thf('114', plain,
% 0.38/0.57      (((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.38/0.57        | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['112', '113'])).
% 0.38/0.57  thf('115', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['73', '74'])).
% 0.38/0.57  thf('116', plain, ((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.38/0.57      inference('demod', [status(thm)], ['114', '115'])).
% 0.38/0.57  thf('117', plain, ($false), inference('demod', [status(thm)], ['6', '116'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
