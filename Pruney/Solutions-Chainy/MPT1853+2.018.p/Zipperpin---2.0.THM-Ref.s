%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z6fXITpWSx

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:04 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 296 expanded)
%              Number of leaves         :   32 (  93 expanded)
%              Depth                    :   19
%              Number of atoms          : 1205 (3647 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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

thf('0',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ X6 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('4',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X16 = X15 )
      | ( v1_subset_1 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,
    ( ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10
       != ( k6_domain_1 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ X10 )
      | ( v1_zfmisc_1 @ X10 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('10',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
       != ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
       != ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(fc6_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('14',plain,(
    ! [X4: $i] :
      ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 )
      | ( v7_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_struct_0])).

thf('15',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('17',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('18',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v7_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('20',plain,(
    ! [X3: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('21',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('23',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v7_struct_0 @ sk_A )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X17 @ X18 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('30',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['32','33'])).

thf(cc10_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v7_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ~ ( v2_struct_0 @ B )
           => ( ~ ( v2_struct_0 @ B )
              & ~ ( v1_tex_2 @ B @ A ) ) ) ) ) )).

thf('35',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ~ ( v1_tex_2 @ X8 @ X9 )
      | ( v2_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v7_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc10_tex_2])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ~ ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['27','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('42',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['39','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['25','49'])).

thf('51',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['26'])).

thf('52',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['32','33'])).

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

thf('53',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( ( sk_C @ X12 @ X13 )
        = ( u1_struct_0 @ X12 ) )
      | ( v1_tex_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('54',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['32','33'])).

thf('60',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( m1_subset_1 @ ( sk_C @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v1_tex_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('61',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['58','63'])).

thf('65',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X16 = X15 )
      | ( v1_subset_1 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('68',plain,
    ( ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('70',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ~ ( v1_subset_1 @ ( sk_C @ X12 @ X13 ) @ ( u1_struct_0 @ X13 ) )
      | ( v1_tex_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('71',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['32','33'])).

thf('74',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('76',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['68','76'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('78',plain,(
    ! [X5: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ~ ( v7_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('79',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
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

thf('81',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('82',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['32','33'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('88',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X2 )
      | ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('89',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('93',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['79','86','93'])).

thf('95',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['26'])).

thf(t6_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
              & ( v1_zfmisc_1 @ A ) ) ) ) )).

thf('96',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ X22 )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ X22 @ X21 ) @ X22 )
      | ~ ( v1_zfmisc_1 @ X22 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t6_tex_2])).

thf('97',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['94','99'])).

thf('101',plain,(
    ! [X3: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('102',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','50','51','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.z6fXITpWSx
% 0.13/0.37  % Computer   : n002.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 12:38:07 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.24/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.52  % Solved by: fo/fo7.sh
% 0.24/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.52  % done 124 iterations in 0.055s
% 0.24/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.52  % SZS output start Refutation
% 0.24/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.24/0.52  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.24/0.52  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.24/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.52  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.24/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.24/0.52  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.24/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.24/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.52  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.24/0.52  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.24/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.24/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.24/0.52  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.24/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.24/0.52  thf(t20_tex_2, conjecture,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.52       ( ![B:$i]:
% 0.24/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.52           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.24/0.52             ( v1_subset_1 @
% 0.24/0.52               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.24/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.52    (~( ![A:$i]:
% 0.24/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.52          ( ![B:$i]:
% 0.24/0.52            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.24/0.52              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.24/0.52                ( v1_subset_1 @
% 0.24/0.52                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.24/0.52                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.24/0.52    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.24/0.52  thf('0', plain,
% 0.24/0.52      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.24/0.52           (u1_struct_0 @ sk_A))
% 0.24/0.52        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('1', plain,
% 0.24/0.52      (~
% 0.24/0.52       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.24/0.52         (u1_struct_0 @ sk_A))) | 
% 0.24/0.52       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.24/0.52      inference('split', [status(esa)], ['0'])).
% 0.24/0.52  thf('2', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(dt_k6_domain_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.24/0.52       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.24/0.52  thf('3', plain,
% 0.24/0.52      (![X6 : $i, X7 : $i]:
% 0.24/0.52         ((v1_xboole_0 @ X6)
% 0.24/0.52          | ~ (m1_subset_1 @ X7 @ X6)
% 0.24/0.52          | (m1_subset_1 @ (k6_domain_1 @ X6 @ X7) @ (k1_zfmisc_1 @ X6)))),
% 0.24/0.52      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.24/0.52  thf('4', plain,
% 0.24/0.52      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.24/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.24/0.52  thf(d7_subset_1, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.24/0.52       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.24/0.52  thf('5', plain,
% 0.24/0.52      (![X15 : $i, X16 : $i]:
% 0.24/0.52         (((X16) = (X15))
% 0.24/0.52          | (v1_subset_1 @ X16 @ X15)
% 0.24/0.52          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.24/0.52      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.24/0.52  thf('6', plain,
% 0.24/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.52        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.24/0.52           (u1_struct_0 @ sk_A))
% 0.24/0.52        | ((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.24/0.52  thf('7', plain,
% 0.24/0.52      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.24/0.52           (u1_struct_0 @ sk_A)))
% 0.24/0.52         <= (~
% 0.24/0.52             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.24/0.52               (u1_struct_0 @ sk_A))))),
% 0.24/0.52      inference('split', [status(esa)], ['0'])).
% 0.24/0.52  thf('8', plain,
% 0.24/0.52      (((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.24/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.24/0.52         <= (~
% 0.24/0.52             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.24/0.52               (u1_struct_0 @ sk_A))))),
% 0.24/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.24/0.52  thf(d1_tex_2, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.24/0.52       ( ( v1_zfmisc_1 @ A ) <=>
% 0.24/0.52         ( ?[B:$i]:
% 0.24/0.52           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.24/0.52  thf('9', plain,
% 0.24/0.52      (![X10 : $i, X11 : $i]:
% 0.24/0.52         (((X10) != (k6_domain_1 @ X10 @ X11))
% 0.24/0.52          | ~ (m1_subset_1 @ X11 @ X10)
% 0.24/0.52          | (v1_zfmisc_1 @ X10)
% 0.24/0.52          | (v1_xboole_0 @ X10))),
% 0.24/0.52      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.24/0.52  thf('10', plain,
% 0.24/0.52      (((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.24/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.52         | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.24/0.52         | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.24/0.52         <= (~
% 0.24/0.52             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.24/0.52               (u1_struct_0 @ sk_A))))),
% 0.24/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.24/0.52  thf('11', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('12', plain,
% 0.24/0.52      (((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.24/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.52         | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.24/0.52         <= (~
% 0.24/0.52             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.24/0.52               (u1_struct_0 @ sk_A))))),
% 0.24/0.52      inference('demod', [status(thm)], ['10', '11'])).
% 0.24/0.52  thf('13', plain,
% 0.24/0.52      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.24/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.24/0.52         <= (~
% 0.24/0.52             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.24/0.52               (u1_struct_0 @ sk_A))))),
% 0.24/0.52      inference('simplify', [status(thm)], ['12'])).
% 0.24/0.52  thf(fc6_struct_0, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( ( ~( v7_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.24/0.52       ( ~( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.24/0.52  thf('14', plain,
% 0.24/0.52      (![X4 : $i]:
% 0.24/0.52         (~ (v1_zfmisc_1 @ (u1_struct_0 @ X4))
% 0.24/0.52          | ~ (l1_struct_0 @ X4)
% 0.24/0.52          | (v7_struct_0 @ X4))),
% 0.24/0.52      inference('cnf', [status(esa)], [fc6_struct_0])).
% 0.24/0.52  thf('15', plain,
% 0.24/0.52      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.52         | (v7_struct_0 @ sk_A)
% 0.24/0.52         | ~ (l1_struct_0 @ sk_A)))
% 0.24/0.52         <= (~
% 0.24/0.52             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.24/0.52               (u1_struct_0 @ sk_A))))),
% 0.24/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.24/0.52  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(dt_l1_pre_topc, axiom,
% 0.24/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.24/0.52  thf('17', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.24/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.24/0.52  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 0.24/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.24/0.52  thf('19', plain,
% 0.24/0.52      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v7_struct_0 @ sk_A)))
% 0.24/0.52         <= (~
% 0.24/0.52             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.24/0.52               (u1_struct_0 @ sk_A))))),
% 0.24/0.52      inference('demod', [status(thm)], ['15', '18'])).
% 0.24/0.52  thf(fc2_struct_0, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.24/0.52       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.24/0.52  thf('20', plain,
% 0.24/0.52      (![X3 : $i]:
% 0.24/0.52         (~ (v1_xboole_0 @ (u1_struct_0 @ X3))
% 0.24/0.52          | ~ (l1_struct_0 @ X3)
% 0.24/0.52          | (v2_struct_0 @ X3))),
% 0.24/0.52      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.24/0.52  thf('21', plain,
% 0.24/0.52      ((((v7_struct_0 @ sk_A) | (v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.24/0.52         <= (~
% 0.24/0.52             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.24/0.52               (u1_struct_0 @ sk_A))))),
% 0.24/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.24/0.52  thf('22', plain, ((l1_struct_0 @ sk_A)),
% 0.24/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.24/0.52  thf('23', plain,
% 0.24/0.52      ((((v7_struct_0 @ sk_A) | (v2_struct_0 @ sk_A)))
% 0.24/0.52         <= (~
% 0.24/0.52             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.24/0.52               (u1_struct_0 @ sk_A))))),
% 0.24/0.52      inference('demod', [status(thm)], ['21', '22'])).
% 0.24/0.52  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('25', plain,
% 0.24/0.52      (((v7_struct_0 @ sk_A))
% 0.24/0.52         <= (~
% 0.24/0.52             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.24/0.52               (u1_struct_0 @ sk_A))))),
% 0.24/0.52      inference('clc', [status(thm)], ['23', '24'])).
% 0.24/0.52  thf('26', plain,
% 0.24/0.52      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.24/0.52         (u1_struct_0 @ sk_A))
% 0.24/0.52        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('27', plain,
% 0.24/0.52      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.24/0.52         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.24/0.52      inference('split', [status(esa)], ['26'])).
% 0.24/0.52  thf('28', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(dt_k1_tex_2, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.24/0.52         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.52       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.24/0.52         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.24/0.52         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.24/0.52  thf('29', plain,
% 0.24/0.52      (![X17 : $i, X18 : $i]:
% 0.24/0.52         (~ (l1_pre_topc @ X17)
% 0.24/0.52          | (v2_struct_0 @ X17)
% 0.24/0.52          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.24/0.52          | (m1_pre_topc @ (k1_tex_2 @ X17 @ X18) @ X17))),
% 0.24/0.52      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.24/0.52  thf('30', plain,
% 0.24/0.52      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.24/0.52        | (v2_struct_0 @ sk_A)
% 0.24/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.24/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.24/0.52  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('32', plain,
% 0.24/0.52      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.24/0.52        | (v2_struct_0 @ sk_A))),
% 0.24/0.52      inference('demod', [status(thm)], ['30', '31'])).
% 0.24/0.52  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('34', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.24/0.52      inference('clc', [status(thm)], ['32', '33'])).
% 0.24/0.52  thf(cc10_tex_2, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.24/0.52       ( ![B:$i]:
% 0.24/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.24/0.52           ( ( ~( v2_struct_0 @ B ) ) =>
% 0.24/0.52             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tex_2 @ B @ A ) ) ) ) ) ) ))).
% 0.24/0.52  thf('35', plain,
% 0.24/0.52      (![X8 : $i, X9 : $i]:
% 0.24/0.52         (~ (m1_pre_topc @ X8 @ X9)
% 0.24/0.52          | ~ (v1_tex_2 @ X8 @ X9)
% 0.24/0.52          | (v2_struct_0 @ X8)
% 0.24/0.52          | ~ (l1_pre_topc @ X9)
% 0.24/0.52          | ~ (v7_struct_0 @ X9)
% 0.24/0.52          | (v2_struct_0 @ X9))),
% 0.24/0.52      inference('cnf', [status(esa)], [cc10_tex_2])).
% 0.24/0.52  thf('36', plain,
% 0.24/0.52      (((v2_struct_0 @ sk_A)
% 0.24/0.52        | ~ (v7_struct_0 @ sk_A)
% 0.24/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.24/0.52        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.24/0.52        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.24/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.24/0.52  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('38', plain,
% 0.24/0.52      (((v2_struct_0 @ sk_A)
% 0.24/0.52        | ~ (v7_struct_0 @ sk_A)
% 0.24/0.52        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.24/0.52        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.24/0.52      inference('demod', [status(thm)], ['36', '37'])).
% 0.24/0.52  thf('39', plain,
% 0.24/0.52      ((((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.24/0.52         | ~ (v7_struct_0 @ sk_A)
% 0.24/0.52         | (v2_struct_0 @ sk_A)))
% 0.24/0.52         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['27', '38'])).
% 0.24/0.52  thf('40', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('41', plain,
% 0.24/0.52      (![X17 : $i, X18 : $i]:
% 0.24/0.52         (~ (l1_pre_topc @ X17)
% 0.24/0.52          | (v2_struct_0 @ X17)
% 0.24/0.52          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.24/0.52          | ~ (v2_struct_0 @ (k1_tex_2 @ X17 @ X18)))),
% 0.24/0.52      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.24/0.52  thf('42', plain,
% 0.24/0.52      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.24/0.52        | (v2_struct_0 @ sk_A)
% 0.24/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.24/0.52      inference('sup-', [status(thm)], ['40', '41'])).
% 0.24/0.52  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('44', plain,
% 0.24/0.52      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.24/0.52      inference('demod', [status(thm)], ['42', '43'])).
% 0.24/0.52  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('46', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.24/0.52      inference('clc', [status(thm)], ['44', '45'])).
% 0.24/0.52  thf('47', plain,
% 0.24/0.52      ((((v2_struct_0 @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 0.24/0.52         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.24/0.52      inference('clc', [status(thm)], ['39', '46'])).
% 0.24/0.52  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('49', plain,
% 0.24/0.52      ((~ (v7_struct_0 @ sk_A))
% 0.24/0.52         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.24/0.52      inference('clc', [status(thm)], ['47', '48'])).
% 0.24/0.52  thf('50', plain,
% 0.24/0.52      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.24/0.52         (u1_struct_0 @ sk_A))) | 
% 0.24/0.52       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.24/0.52      inference('sup-', [status(thm)], ['25', '49'])).
% 0.24/0.52  thf('51', plain,
% 0.24/0.52      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.24/0.52         (u1_struct_0 @ sk_A))) | 
% 0.24/0.52       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.24/0.52      inference('split', [status(esa)], ['26'])).
% 0.24/0.52  thf('52', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.24/0.52      inference('clc', [status(thm)], ['32', '33'])).
% 0.24/0.52  thf(d3_tex_2, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( l1_pre_topc @ A ) =>
% 0.24/0.52       ( ![B:$i]:
% 0.24/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.24/0.52           ( ( v1_tex_2 @ B @ A ) <=>
% 0.24/0.52             ( ![C:$i]:
% 0.24/0.52               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.52                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.24/0.52                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.24/0.52  thf('53', plain,
% 0.24/0.52      (![X12 : $i, X13 : $i]:
% 0.24/0.52         (~ (m1_pre_topc @ X12 @ X13)
% 0.24/0.52          | ((sk_C @ X12 @ X13) = (u1_struct_0 @ X12))
% 0.24/0.52          | (v1_tex_2 @ X12 @ X13)
% 0.24/0.52          | ~ (l1_pre_topc @ X13))),
% 0.24/0.52      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.24/0.52  thf('54', plain,
% 0.24/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.24/0.52        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.24/0.52        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.24/0.52            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.24/0.52      inference('sup-', [status(thm)], ['52', '53'])).
% 0.24/0.52  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('56', plain,
% 0.24/0.52      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.24/0.52        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.24/0.52            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.24/0.52      inference('demod', [status(thm)], ['54', '55'])).
% 0.24/0.52  thf('57', plain,
% 0.24/0.52      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.24/0.52         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.24/0.52      inference('split', [status(esa)], ['0'])).
% 0.24/0.52  thf('58', plain,
% 0.24/0.52      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.24/0.52          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.24/0.52         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['56', '57'])).
% 0.24/0.52  thf('59', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.24/0.52      inference('clc', [status(thm)], ['32', '33'])).
% 0.24/0.52  thf('60', plain,
% 0.24/0.52      (![X12 : $i, X13 : $i]:
% 0.24/0.52         (~ (m1_pre_topc @ X12 @ X13)
% 0.24/0.52          | (m1_subset_1 @ (sk_C @ X12 @ X13) @ 
% 0.24/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.24/0.52          | (v1_tex_2 @ X12 @ X13)
% 0.24/0.52          | ~ (l1_pre_topc @ X13))),
% 0.24/0.52      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.24/0.52  thf('61', plain,
% 0.24/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.24/0.52        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.24/0.52        | (m1_subset_1 @ (sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A) @ 
% 0.24/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.24/0.52      inference('sup-', [status(thm)], ['59', '60'])).
% 0.24/0.52  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('63', plain,
% 0.24/0.52      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.24/0.52        | (m1_subset_1 @ (sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A) @ 
% 0.24/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.24/0.52      inference('demod', [status(thm)], ['61', '62'])).
% 0.24/0.52  thf('64', plain,
% 0.24/0.52      ((((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.24/0.52          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.52         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))
% 0.24/0.52         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.24/0.52      inference('sup+', [status(thm)], ['58', '63'])).
% 0.24/0.52  thf('65', plain,
% 0.24/0.52      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.24/0.52         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.24/0.52      inference('split', [status(esa)], ['0'])).
% 0.24/0.52  thf('66', plain,
% 0.24/0.52      (((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.24/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.24/0.52         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.24/0.52      inference('clc', [status(thm)], ['64', '65'])).
% 0.24/0.52  thf('67', plain,
% 0.24/0.52      (![X15 : $i, X16 : $i]:
% 0.24/0.52         (((X16) = (X15))
% 0.24/0.52          | (v1_subset_1 @ X16 @ X15)
% 0.24/0.52          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.24/0.52      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.24/0.52  thf('68', plain,
% 0.24/0.52      ((((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.24/0.52          (u1_struct_0 @ sk_A))
% 0.24/0.52         | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))))
% 0.24/0.52         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['66', '67'])).
% 0.24/0.52  thf('69', plain,
% 0.24/0.52      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.24/0.52          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.24/0.52         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['56', '57'])).
% 0.24/0.52  thf('70', plain,
% 0.24/0.52      (![X12 : $i, X13 : $i]:
% 0.24/0.52         (~ (m1_pre_topc @ X12 @ X13)
% 0.24/0.52          | ~ (v1_subset_1 @ (sk_C @ X12 @ X13) @ (u1_struct_0 @ X13))
% 0.24/0.52          | (v1_tex_2 @ X12 @ X13)
% 0.24/0.52          | ~ (l1_pre_topc @ X13))),
% 0.24/0.52      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.24/0.52  thf('71', plain,
% 0.24/0.52      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.24/0.52            (u1_struct_0 @ sk_A))
% 0.24/0.52         | ~ (l1_pre_topc @ sk_A)
% 0.24/0.52         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.24/0.52         | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))
% 0.24/0.52         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['69', '70'])).
% 0.24/0.52  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('73', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.24/0.52      inference('clc', [status(thm)], ['32', '33'])).
% 0.24/0.52  thf('74', plain,
% 0.24/0.52      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.24/0.52            (u1_struct_0 @ sk_A))
% 0.24/0.52         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))
% 0.24/0.52         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.24/0.52      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.24/0.52  thf('75', plain,
% 0.24/0.52      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.24/0.52         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.24/0.52      inference('split', [status(esa)], ['0'])).
% 0.24/0.52  thf('76', plain,
% 0.24/0.52      ((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.24/0.52           (u1_struct_0 @ sk_A)))
% 0.24/0.52         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.24/0.52      inference('clc', [status(thm)], ['74', '75'])).
% 0.24/0.52  thf('77', plain,
% 0.24/0.52      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))
% 0.24/0.52         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.24/0.52      inference('clc', [status(thm)], ['68', '76'])).
% 0.24/0.52  thf(fc7_struct_0, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.24/0.52       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.24/0.52  thf('78', plain,
% 0.24/0.52      (![X5 : $i]:
% 0.24/0.52         ((v1_zfmisc_1 @ (u1_struct_0 @ X5))
% 0.24/0.52          | ~ (l1_struct_0 @ X5)
% 0.24/0.52          | ~ (v7_struct_0 @ X5))),
% 0.24/0.52      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.24/0.52  thf('79', plain,
% 0.24/0.52      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.24/0.52         | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.24/0.52         | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.24/0.52         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.24/0.52      inference('sup+', [status(thm)], ['77', '78'])).
% 0.24/0.52  thf('80', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf(fc2_tex_2, axiom,
% 0.24/0.52    (![A:$i,B:$i]:
% 0.24/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.24/0.52         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.24/0.52       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.24/0.52         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.24/0.52         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.24/0.52  thf('81', plain,
% 0.24/0.52      (![X19 : $i, X20 : $i]:
% 0.24/0.52         (~ (l1_pre_topc @ X19)
% 0.24/0.52          | (v2_struct_0 @ X19)
% 0.24/0.52          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.24/0.52          | (v7_struct_0 @ (k1_tex_2 @ X19 @ X20)))),
% 0.24/0.52      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.24/0.52  thf('82', plain,
% 0.24/0.52      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.24/0.52        | (v2_struct_0 @ sk_A)
% 0.24/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.24/0.52      inference('sup-', [status(thm)], ['80', '81'])).
% 0.24/0.52  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('84', plain,
% 0.24/0.52      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.24/0.52      inference('demod', [status(thm)], ['82', '83'])).
% 0.24/0.52  thf('85', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('86', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.24/0.52      inference('clc', [status(thm)], ['84', '85'])).
% 0.24/0.52  thf('87', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.24/0.52      inference('clc', [status(thm)], ['32', '33'])).
% 0.24/0.52  thf(dt_m1_pre_topc, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( l1_pre_topc @ A ) =>
% 0.24/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.24/0.52  thf('88', plain,
% 0.24/0.52      (![X1 : $i, X2 : $i]:
% 0.24/0.52         (~ (m1_pre_topc @ X1 @ X2) | (l1_pre_topc @ X1) | ~ (l1_pre_topc @ X2))),
% 0.24/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.24/0.52  thf('89', plain,
% 0.24/0.52      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.24/0.52      inference('sup-', [status(thm)], ['87', '88'])).
% 0.24/0.52  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('91', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.24/0.52      inference('demod', [status(thm)], ['89', '90'])).
% 0.24/0.52  thf('92', plain, (![X0 : $i]: ((l1_struct_0 @ X0) | ~ (l1_pre_topc @ X0))),
% 0.24/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.24/0.52  thf('93', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.24/0.52      inference('sup-', [status(thm)], ['91', '92'])).
% 0.24/0.52  thf('94', plain,
% 0.24/0.52      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.24/0.52         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.24/0.52      inference('demod', [status(thm)], ['79', '86', '93'])).
% 0.24/0.52  thf('95', plain,
% 0.24/0.52      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.24/0.52         (u1_struct_0 @ sk_A)))
% 0.24/0.52         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.24/0.52               (u1_struct_0 @ sk_A))))),
% 0.24/0.52      inference('split', [status(esa)], ['26'])).
% 0.24/0.52  thf(t6_tex_2, axiom,
% 0.24/0.52    (![A:$i]:
% 0.24/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.24/0.52       ( ![B:$i]:
% 0.24/0.52         ( ( m1_subset_1 @ B @ A ) =>
% 0.24/0.52           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.24/0.52                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.24/0.52  thf('96', plain,
% 0.24/0.52      (![X21 : $i, X22 : $i]:
% 0.24/0.52         (~ (m1_subset_1 @ X21 @ X22)
% 0.24/0.52          | ~ (v1_subset_1 @ (k6_domain_1 @ X22 @ X21) @ X22)
% 0.24/0.52          | ~ (v1_zfmisc_1 @ X22)
% 0.24/0.52          | (v1_xboole_0 @ X22))),
% 0.24/0.52      inference('cnf', [status(esa)], [t6_tex_2])).
% 0.24/0.52  thf('97', plain,
% 0.24/0.52      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.52         | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.24/0.52         | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.24/0.52         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.24/0.52               (u1_struct_0 @ sk_A))))),
% 0.24/0.52      inference('sup-', [status(thm)], ['95', '96'])).
% 0.24/0.52  thf('98', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('99', plain,
% 0.24/0.52      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.24/0.52         | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.24/0.52         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.24/0.52               (u1_struct_0 @ sk_A))))),
% 0.24/0.52      inference('demod', [status(thm)], ['97', '98'])).
% 0.24/0.52  thf('100', plain,
% 0.24/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.24/0.52         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) & 
% 0.24/0.52             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.24/0.52               (u1_struct_0 @ sk_A))))),
% 0.24/0.52      inference('sup-', [status(thm)], ['94', '99'])).
% 0.24/0.52  thf('101', plain,
% 0.24/0.52      (![X3 : $i]:
% 0.24/0.52         (~ (v1_xboole_0 @ (u1_struct_0 @ X3))
% 0.24/0.52          | ~ (l1_struct_0 @ X3)
% 0.24/0.52          | (v2_struct_0 @ X3))),
% 0.24/0.52      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.24/0.52  thf('102', plain,
% 0.24/0.52      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.24/0.52         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) & 
% 0.24/0.52             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.24/0.52               (u1_struct_0 @ sk_A))))),
% 0.24/0.52      inference('sup-', [status(thm)], ['100', '101'])).
% 0.24/0.52  thf('103', plain, ((l1_struct_0 @ sk_A)),
% 0.24/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.24/0.52  thf('104', plain,
% 0.24/0.52      (((v2_struct_0 @ sk_A))
% 0.24/0.52         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) & 
% 0.24/0.52             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.24/0.52               (u1_struct_0 @ sk_A))))),
% 0.24/0.52      inference('demod', [status(thm)], ['102', '103'])).
% 0.24/0.52  thf('105', plain, (~ (v2_struct_0 @ sk_A)),
% 0.24/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.52  thf('106', plain,
% 0.24/0.52      (~
% 0.24/0.52       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.24/0.52         (u1_struct_0 @ sk_A))) | 
% 0.24/0.52       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.24/0.52      inference('sup-', [status(thm)], ['104', '105'])).
% 0.24/0.52  thf('107', plain, ($false),
% 0.24/0.52      inference('sat_resolution*', [status(thm)], ['1', '50', '51', '106'])).
% 0.24/0.52  
% 0.24/0.52  % SZS output end Refutation
% 0.24/0.52  
% 0.24/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
