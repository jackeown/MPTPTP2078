%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DWSaynmc3q

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 490 expanded)
%              Number of leaves         :   30 ( 144 expanded)
%              Depth                    :   18
%              Number of atoms          : 1047 (6499 expanded)
%              Number of equality atoms :   12 (  48 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ X17 )
      | ( v1_subset_1 @ ( k6_domain_1 @ X17 @ X16 ) @ X17 )
      | ( v1_zfmisc_1 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t7_tex_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(cc1_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v1_zfmisc_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_zfmisc_1])).

thf('6',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc6_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('9',plain,(
    ! [X4: $i] :
      ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 )
      | ( v7_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_struct_0])).

thf('10',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('12',plain,(
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v7_struct_0 @ sk_A )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) )
        & ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X12 @ X13 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('19',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['21','22'])).

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

thf('24',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ~ ( v1_tex_2 @ X5 @ X6 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X6 )
      | ~ ( v7_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc10_tex_2])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      | ~ ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('31',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['28','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','38'])).

thf('40',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('41',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('42',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['21','22'])).

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

thf('43',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( ( sk_C @ X7 @ X8 )
        = ( u1_struct_0 @ X7 ) )
      | ( v1_tex_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('44',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['21','22'])).

thf('50',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( m1_subset_1 @ ( sk_C @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( v1_tex_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('51',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['48','53'])).

thf('55',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['54','55'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('57',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X11 = X10 )
      | ( v1_subset_1 @ X11 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('58',plain,
    ( ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('60',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ~ ( v1_subset_1 @ ( sk_C @ X7 @ X8 ) @ ( u1_struct_0 @ X8 ) )
      | ( v1_tex_2 @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('61',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['21','22'])).

thf('64',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['58','66'])).

thf(t8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) )
              & ( v7_struct_0 @ A ) ) ) ) )).

thf('68',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X19 ) @ X18 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( v7_struct_0 @ X19 )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t8_tex_2])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
        | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
        | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['58','66'])).

thf('71',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['21','22'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('72',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('73',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('77',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ) )).

thf('79',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('80',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['58','66'])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','77','84','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','39','40','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DWSaynmc3q
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:35:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 73 iterations in 0.027s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.48  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.48  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.22/0.48  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.22/0.48  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.22/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.22/0.48  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.22/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.48  thf(t20_tex_2, conjecture,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.48           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.22/0.48             ( v1_subset_1 @
% 0.22/0.48               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i]:
% 0.22/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.48          ( ![B:$i]:
% 0.22/0.48            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.48              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.22/0.48                ( v1_subset_1 @
% 0.22/0.48                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.22/0.48                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.22/0.48  thf('0', plain,
% 0.22/0.48      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.48           (u1_struct_0 @ sk_A))
% 0.22/0.48        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('1', plain,
% 0.22/0.48      (~
% 0.22/0.48       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.48         (u1_struct_0 @ sk_A))) | 
% 0.22/0.48       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.48      inference('split', [status(esa)], ['0'])).
% 0.22/0.48  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t7_tex_2, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ B @ A ) =>
% 0.22/0.48           ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) ))).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X16 : $i, X17 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X16 @ X17)
% 0.22/0.48          | (v1_subset_1 @ (k6_domain_1 @ X17 @ X16) @ X17)
% 0.22/0.48          | (v1_zfmisc_1 @ X17)
% 0.22/0.48          | (v1_xboole_0 @ X17))),
% 0.22/0.48      inference('cnf', [status(esa)], [t7_tex_2])).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.22/0.48        | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.22/0.48        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.48           (u1_struct_0 @ sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.48  thf(cc1_zfmisc_1, axiom,
% 0.22/0.48    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_zfmisc_1 @ A ) ))).
% 0.22/0.48  thf('5', plain, (![X0 : $i]: ((v1_zfmisc_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.48      inference('cnf', [status(esa)], [cc1_zfmisc_1])).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.48         (u1_struct_0 @ sk_A))
% 0.22/0.48        | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.48      inference('clc', [status(thm)], ['4', '5'])).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.48           (u1_struct_0 @ sk_A)))
% 0.22/0.48         <= (~
% 0.22/0.48             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.48               (u1_struct_0 @ sk_A))))),
% 0.22/0.48      inference('split', [status(esa)], ['0'])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48         <= (~
% 0.22/0.48             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.48               (u1_struct_0 @ sk_A))))),
% 0.22/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.48  thf(fc6_struct_0, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ( ~( v7_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.48       ( ~( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (![X4 : $i]:
% 0.22/0.48         (~ (v1_zfmisc_1 @ (u1_struct_0 @ X4))
% 0.22/0.48          | ~ (l1_struct_0 @ X4)
% 0.22/0.48          | (v7_struct_0 @ X4))),
% 0.22/0.48      inference('cnf', [status(esa)], [fc6_struct_0])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      ((((v7_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.22/0.48         <= (~
% 0.22/0.48             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.48               (u1_struct_0 @ sk_A))))),
% 0.22/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.48  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(dt_l1_pre_topc, axiom,
% 0.22/0.48    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.48  thf('12', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.48  thf('13', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      (((v7_struct_0 @ sk_A))
% 0.22/0.48         <= (~
% 0.22/0.48             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.48               (u1_struct_0 @ sk_A))))),
% 0.22/0.48      inference('demod', [status(thm)], ['10', '13'])).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.48         (u1_struct_0 @ sk_A))
% 0.22/0.48        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.22/0.48         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.48      inference('split', [status(esa)], ['15'])).
% 0.22/0.48  thf('17', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(dt_k1_tex_2, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.22/0.48         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.48       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.22/0.48         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.22/0.48         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.22/0.48  thf('18', plain,
% 0.22/0.48      (![X12 : $i, X13 : $i]:
% 0.22/0.48         (~ (l1_pre_topc @ X12)
% 0.22/0.48          | (v2_struct_0 @ X12)
% 0.22/0.48          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.22/0.48          | (m1_pre_topc @ (k1_tex_2 @ X12 @ X13) @ X12))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.22/0.48  thf('19', plain,
% 0.22/0.48      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.48        | (v2_struct_0 @ sk_A)
% 0.22/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.48  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('21', plain,
% 0.22/0.48      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['19', '20'])).
% 0.22/0.48  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('23', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.48      inference('clc', [status(thm)], ['21', '22'])).
% 0.22/0.48  thf(cc10_tex_2, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.48           ( ( ~( v2_struct_0 @ B ) ) =>
% 0.22/0.48             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tex_2 @ B @ A ) ) ) ) ) ) ))).
% 0.22/0.48  thf('24', plain,
% 0.22/0.48      (![X5 : $i, X6 : $i]:
% 0.22/0.48         (~ (m1_pre_topc @ X5 @ X6)
% 0.22/0.48          | ~ (v1_tex_2 @ X5 @ X6)
% 0.22/0.48          | (v2_struct_0 @ X5)
% 0.22/0.48          | ~ (l1_pre_topc @ X6)
% 0.22/0.48          | ~ (v7_struct_0 @ X6)
% 0.22/0.48          | (v2_struct_0 @ X6))),
% 0.22/0.48      inference('cnf', [status(esa)], [cc10_tex_2])).
% 0.22/0.48  thf('25', plain,
% 0.22/0.48      (((v2_struct_0 @ sk_A)
% 0.22/0.48        | ~ (v7_struct_0 @ sk_A)
% 0.22/0.48        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.48        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.22/0.48        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.48  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('27', plain,
% 0.22/0.48      (((v2_struct_0 @ sk_A)
% 0.22/0.48        | ~ (v7_struct_0 @ sk_A)
% 0.22/0.48        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.22/0.48        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.48  thf('28', plain,
% 0.22/0.48      ((((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.22/0.48         | ~ (v7_struct_0 @ sk_A)
% 0.22/0.48         | (v2_struct_0 @ sk_A)))
% 0.22/0.48         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['16', '27'])).
% 0.22/0.48  thf('29', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('30', plain,
% 0.22/0.48      (![X12 : $i, X13 : $i]:
% 0.22/0.48         (~ (l1_pre_topc @ X12)
% 0.22/0.48          | (v2_struct_0 @ X12)
% 0.22/0.48          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.22/0.48          | ~ (v2_struct_0 @ (k1_tex_2 @ X12 @ X13)))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.22/0.48  thf('31', plain,
% 0.22/0.48      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.22/0.48        | (v2_struct_0 @ sk_A)
% 0.22/0.48        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.48  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('33', plain,
% 0.22/0.48      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.48  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('35', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.22/0.48      inference('clc', [status(thm)], ['33', '34'])).
% 0.22/0.48  thf('36', plain,
% 0.22/0.48      ((((v2_struct_0 @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 0.22/0.48         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.48      inference('clc', [status(thm)], ['28', '35'])).
% 0.22/0.48  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('38', plain,
% 0.22/0.48      ((~ (v7_struct_0 @ sk_A))
% 0.22/0.48         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.48      inference('clc', [status(thm)], ['36', '37'])).
% 0.22/0.48  thf('39', plain,
% 0.22/0.48      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.48         (u1_struct_0 @ sk_A))) | 
% 0.22/0.48       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['14', '38'])).
% 0.22/0.48  thf('40', plain,
% 0.22/0.48      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.48         (u1_struct_0 @ sk_A))) | 
% 0.22/0.48       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.48      inference('split', [status(esa)], ['15'])).
% 0.22/0.48  thf('41', plain,
% 0.22/0.48      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.48         (u1_struct_0 @ sk_A)))
% 0.22/0.48         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.48               (u1_struct_0 @ sk_A))))),
% 0.22/0.48      inference('split', [status(esa)], ['15'])).
% 0.22/0.48  thf('42', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.48      inference('clc', [status(thm)], ['21', '22'])).
% 0.22/0.48  thf(d3_tex_2, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( l1_pre_topc @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.48           ( ( v1_tex_2 @ B @ A ) <=>
% 0.22/0.48             ( ![C:$i]:
% 0.22/0.48               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.48                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.22/0.48                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.22/0.48  thf('43', plain,
% 0.22/0.48      (![X7 : $i, X8 : $i]:
% 0.22/0.48         (~ (m1_pre_topc @ X7 @ X8)
% 0.22/0.48          | ((sk_C @ X7 @ X8) = (u1_struct_0 @ X7))
% 0.22/0.48          | (v1_tex_2 @ X7 @ X8)
% 0.22/0.48          | ~ (l1_pre_topc @ X8))),
% 0.22/0.48      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.22/0.48  thf('44', plain,
% 0.22/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.48        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.48        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.48            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))),
% 0.22/0.48      inference('sup-', [status(thm)], ['42', '43'])).
% 0.22/0.48  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('46', plain,
% 0.22/0.48      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.48        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.48            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))),
% 0.22/0.48      inference('demod', [status(thm)], ['44', '45'])).
% 0.22/0.48  thf('47', plain,
% 0.22/0.48      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.22/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.48      inference('split', [status(esa)], ['0'])).
% 0.22/0.48  thf('48', plain,
% 0.22/0.48      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.48          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))
% 0.22/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.48  thf('49', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.48      inference('clc', [status(thm)], ['21', '22'])).
% 0.22/0.48  thf('50', plain,
% 0.22/0.48      (![X7 : $i, X8 : $i]:
% 0.22/0.48         (~ (m1_pre_topc @ X7 @ X8)
% 0.22/0.48          | (m1_subset_1 @ (sk_C @ X7 @ X8) @ 
% 0.22/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.22/0.48          | (v1_tex_2 @ X7 @ X8)
% 0.22/0.48          | ~ (l1_pre_topc @ X8))),
% 0.22/0.48      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.22/0.48  thf('51', plain,
% 0.22/0.48      ((~ (l1_pre_topc @ sk_A)
% 0.22/0.48        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.48        | (m1_subset_1 @ (sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) @ 
% 0.22/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.48      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.48  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('53', plain,
% 0.22/0.48      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.48        | (m1_subset_1 @ (sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) @ 
% 0.22/0.48           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.48      inference('demod', [status(thm)], ['51', '52'])).
% 0.22/0.48  thf('54', plain,
% 0.22/0.48      ((((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.22/0.48          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.22/0.48         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))
% 0.22/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.48      inference('sup+', [status(thm)], ['48', '53'])).
% 0.22/0.48  thf('55', plain,
% 0.22/0.48      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.22/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.48      inference('split', [status(esa)], ['0'])).
% 0.22/0.48  thf('56', plain,
% 0.22/0.48      (((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.22/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.22/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.48      inference('clc', [status(thm)], ['54', '55'])).
% 0.22/0.48  thf(d7_subset_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.48       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.22/0.48  thf('57', plain,
% 0.22/0.48      (![X10 : $i, X11 : $i]:
% 0.22/0.48         (((X11) = (X10))
% 0.22/0.48          | (v1_subset_1 @ X11 @ X10)
% 0.22/0.48          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.22/0.48  thf('58', plain,
% 0.22/0.48      ((((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.22/0.48          (u1_struct_0 @ sk_A))
% 0.22/0.48         | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))))
% 0.22/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['56', '57'])).
% 0.22/0.48  thf('59', plain,
% 0.22/0.48      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.48          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))))
% 0.22/0.48         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.48  thf('60', plain,
% 0.22/0.48      (![X7 : $i, X8 : $i]:
% 0.22/0.48         (~ (m1_pre_topc @ X7 @ X8)
% 0.22/0.48          | ~ (v1_subset_1 @ (sk_C @ X7 @ X8) @ (u1_struct_0 @ X8))
% 0.22/0.48          | (v1_tex_2 @ X7 @ X8)
% 0.22/0.48          | ~ (l1_pre_topc @ X8))),
% 0.22/0.48      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.22/0.49  thf('61', plain,
% 0.22/0.49      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.22/0.49            (u1_struct_0 @ sk_A))
% 0.22/0.49         | ~ (l1_pre_topc @ sk_A)
% 0.22/0.49         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.22/0.49         | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))
% 0.22/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['59', '60'])).
% 0.22/0.49  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('63', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.49      inference('clc', [status(thm)], ['21', '22'])).
% 0.22/0.49  thf('64', plain,
% 0.22/0.49      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.22/0.49            (u1_struct_0 @ sk_A))
% 0.22/0.49         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))
% 0.22/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.49      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.22/0.49  thf('65', plain,
% 0.22/0.49      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.22/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('66', plain,
% 0.22/0.49      ((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ 
% 0.22/0.49           (u1_struct_0 @ sk_A)))
% 0.22/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.49      inference('clc', [status(thm)], ['64', '65'])).
% 0.22/0.49  thf('67', plain,
% 0.22/0.49      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))
% 0.22/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.49      inference('clc', [status(thm)], ['58', '66'])).
% 0.22/0.49  thf(t8_tex_2, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.49           ( ~( ( v1_subset_1 @
% 0.22/0.49                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.22/0.49                  ( u1_struct_0 @ A ) ) & 
% 0.22/0.49                ( v7_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.49  thf('68', plain,
% 0.22/0.49      (![X18 : $i, X19 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.22/0.49          | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X19) @ X18) @ 
% 0.22/0.49               (u1_struct_0 @ X19))
% 0.22/0.49          | ~ (v7_struct_0 @ X19)
% 0.22/0.49          | ~ (l1_struct_0 @ X19)
% 0.22/0.49          | (v2_struct_0 @ X19))),
% 0.22/0.49      inference('cnf', [status(esa)], [t8_tex_2])).
% 0.22/0.49  thf('69', plain,
% 0.22/0.49      ((![X0 : $i]:
% 0.22/0.49          (~ (v1_subset_1 @ 
% 0.22/0.49              (k6_domain_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) @ X0) @ 
% 0.22/0.49              (u1_struct_0 @ sk_A))
% 0.22/0.49           | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.22/0.49           | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.22/0.49           | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.22/0.49           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))))
% 0.22/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['67', '68'])).
% 0.22/0.49  thf('70', plain,
% 0.22/0.49      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))
% 0.22/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.49      inference('clc', [status(thm)], ['58', '66'])).
% 0.22/0.49  thf('71', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.49      inference('clc', [status(thm)], ['21', '22'])).
% 0.22/0.49  thf(dt_m1_pre_topc, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.49  thf('72', plain,
% 0.22/0.49      (![X2 : $i, X3 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X2 @ X3) | (l1_pre_topc @ X2) | ~ (l1_pre_topc @ X3))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.49  thf('73', plain,
% 0.22/0.49      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['71', '72'])).
% 0.22/0.49  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('75', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.22/0.49      inference('demod', [status(thm)], ['73', '74'])).
% 0.22/0.49  thf('76', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.49  thf('77', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['75', '76'])).
% 0.22/0.49  thf('78', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(fc2_tex_2, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.22/0.49         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.49       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.22/0.49         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.22/0.49         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.22/0.49  thf('79', plain,
% 0.22/0.49      (![X14 : $i, X15 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X14)
% 0.22/0.49          | (v2_struct_0 @ X14)
% 0.22/0.49          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.22/0.49          | (v7_struct_0 @ (k1_tex_2 @ X14 @ X15)))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.22/0.49  thf('80', plain,
% 0.22/0.49      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.22/0.49        | (v2_struct_0 @ sk_A)
% 0.22/0.49        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['78', '79'])).
% 0.22/0.49  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('82', plain,
% 0.22/0.49      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['80', '81'])).
% 0.22/0.49  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('84', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.22/0.49      inference('clc', [status(thm)], ['82', '83'])).
% 0.22/0.49  thf('85', plain,
% 0.22/0.49      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))
% 0.22/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.49      inference('clc', [status(thm)], ['58', '66'])).
% 0.22/0.49  thf('86', plain,
% 0.22/0.49      ((![X0 : $i]:
% 0.22/0.49          (~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 0.22/0.49              (u1_struct_0 @ sk_A))
% 0.22/0.49           | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.22/0.49           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.22/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.49      inference('demod', [status(thm)], ['69', '70', '77', '84', '85'])).
% 0.22/0.49  thf('87', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.22/0.49      inference('clc', [status(thm)], ['33', '34'])).
% 0.22/0.49  thf('88', plain,
% 0.22/0.49      ((![X0 : $i]:
% 0.22/0.49          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.22/0.49           | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 0.22/0.49                (u1_struct_0 @ sk_A))))
% 0.22/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.22/0.49      inference('clc', [status(thm)], ['86', '87'])).
% 0.22/0.49  thf('89', plain,
% 0.22/0.49      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.22/0.49         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)) & 
% 0.22/0.49             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.49               (u1_struct_0 @ sk_A))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['41', '88'])).
% 0.22/0.49  thf('90', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('91', plain,
% 0.22/0.49      (~
% 0.22/0.49       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.22/0.49         (u1_struct_0 @ sk_A))) | 
% 0.22/0.49       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.49      inference('demod', [status(thm)], ['89', '90'])).
% 0.22/0.49  thf('92', plain, ($false),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['1', '39', '40', '91'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
