%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9b6EJp2gQh

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 176 expanded)
%              Number of leaves         :   26 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :  713 (2065 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

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
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ X12 )
      | ( v1_subset_1 @ ( k6_domain_1 @ X12 @ X11 ) @ X12 )
      | ( v1_zfmisc_1 @ X12 )
      | ( v1_xboole_0 @ X12 ) ) ),
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
    ! [X2: $i] :
      ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 )
      | ( v7_struct_0 @ X2 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X7 @ X8 ) @ X7 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ~ ( v1_tex_2 @ X3 @ X4 )
      | ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v7_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ( v2_struct_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X7 @ X8 ) ) ) ),
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

thf('41',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['21','22'])).

thf(cc13_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ~ ( v7_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( ~ ( v2_struct_0 @ B )
              & ~ ( v1_tex_2 @ B @ A ) )
           => ( ~ ( v2_struct_0 @ B )
              & ~ ( v7_struct_0 @ B ) ) ) ) ) )).

thf('42',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ~ ( v7_struct_0 @ X5 )
      | ( v1_tex_2 @ X5 @ X6 )
      | ( v2_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X6 )
      | ( v7_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc13_tex_2])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v7_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
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

thf('46',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('47',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v7_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['43','44','51'])).

thf('53',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,
    ( ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) )
      | ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('56',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v7_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v7_struct_0 @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf(t8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) )
              & ( v7_struct_0 @ A ) ) ) ) )).

thf('60',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X14 ) @ X13 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( v7_struct_0 @ X14 )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t8_tex_2])).

thf('61',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['58','66'])).

thf('68',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','39','40','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9b6EJp2gQh
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:01:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.44  % Solved by: fo/fo7.sh
% 0.20/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.44  % done 40 iterations in 0.018s
% 0.20/0.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.44  % SZS output start Refutation
% 0.20/0.44  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.44  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.44  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.44  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.44  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.20/0.44  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.44  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.44  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.20/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.44  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.20/0.44  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.44  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.44  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.44  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.44  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.20/0.44  thf(t20_tex_2, conjecture,
% 0.20/0.44    (![A:$i]:
% 0.20/0.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.44       ( ![B:$i]:
% 0.20/0.44         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.44           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.20/0.44             ( v1_subset_1 @
% 0.20/0.44               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.44    (~( ![A:$i]:
% 0.20/0.44        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.44          ( ![B:$i]:
% 0.20/0.44            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.44              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.20/0.44                ( v1_subset_1 @
% 0.20/0.44                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.20/0.44                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.20/0.44    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.20/0.44  thf('0', plain,
% 0.20/0.44      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.44           (u1_struct_0 @ sk_A))
% 0.20/0.44        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('1', plain,
% 0.20/0.44      (~
% 0.20/0.44       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.44         (u1_struct_0 @ sk_A))) | 
% 0.20/0.44       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.44      inference('split', [status(esa)], ['0'])).
% 0.20/0.44  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(t7_tex_2, axiom,
% 0.20/0.44    (![A:$i]:
% 0.20/0.44     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.44       ( ![B:$i]:
% 0.20/0.44         ( ( m1_subset_1 @ B @ A ) =>
% 0.20/0.44           ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) ))).
% 0.20/0.44  thf('3', plain,
% 0.20/0.44      (![X11 : $i, X12 : $i]:
% 0.20/0.44         (~ (m1_subset_1 @ X11 @ X12)
% 0.20/0.44          | (v1_subset_1 @ (k6_domain_1 @ X12 @ X11) @ X12)
% 0.20/0.44          | (v1_zfmisc_1 @ X12)
% 0.20/0.44          | (v1_xboole_0 @ X12))),
% 0.20/0.44      inference('cnf', [status(esa)], [t7_tex_2])).
% 0.20/0.44  thf('4', plain,
% 0.20/0.44      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.44        | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.44        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.44           (u1_struct_0 @ sk_A)))),
% 0.20/0.44      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.44  thf(cc1_zfmisc_1, axiom,
% 0.20/0.44    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_zfmisc_1 @ A ) ))).
% 0.20/0.44  thf('5', plain, (![X0 : $i]: ((v1_zfmisc_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.44      inference('cnf', [status(esa)], [cc1_zfmisc_1])).
% 0.20/0.44  thf('6', plain,
% 0.20/0.44      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.44         (u1_struct_0 @ sk_A))
% 0.20/0.44        | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.44      inference('clc', [status(thm)], ['4', '5'])).
% 0.20/0.44  thf('7', plain,
% 0.20/0.44      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.44           (u1_struct_0 @ sk_A)))
% 0.20/0.44         <= (~
% 0.20/0.44             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.44               (u1_struct_0 @ sk_A))))),
% 0.20/0.44      inference('split', [status(esa)], ['0'])).
% 0.20/0.44  thf('8', plain,
% 0.20/0.44      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.44         <= (~
% 0.20/0.44             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.44               (u1_struct_0 @ sk_A))))),
% 0.20/0.44      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.44  thf(fc6_struct_0, axiom,
% 0.20/0.44    (![A:$i]:
% 0.20/0.44     ( ( ( ~( v7_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.44       ( ~( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.44  thf('9', plain,
% 0.20/0.44      (![X2 : $i]:
% 0.20/0.44         (~ (v1_zfmisc_1 @ (u1_struct_0 @ X2))
% 0.20/0.44          | ~ (l1_struct_0 @ X2)
% 0.20/0.44          | (v7_struct_0 @ X2))),
% 0.20/0.44      inference('cnf', [status(esa)], [fc6_struct_0])).
% 0.20/0.44  thf('10', plain,
% 0.20/0.44      ((((v7_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.20/0.44         <= (~
% 0.20/0.44             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.44               (u1_struct_0 @ sk_A))))),
% 0.20/0.44      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.44  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(dt_l1_pre_topc, axiom,
% 0.20/0.44    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.44  thf('12', plain, (![X1 : $i]: ((l1_struct_0 @ X1) | ~ (l1_pre_topc @ X1))),
% 0.20/0.44      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.44  thf('13', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.44      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.44  thf('14', plain,
% 0.20/0.44      (((v7_struct_0 @ sk_A))
% 0.20/0.44         <= (~
% 0.20/0.44             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.44               (u1_struct_0 @ sk_A))))),
% 0.20/0.44      inference('demod', [status(thm)], ['10', '13'])).
% 0.20/0.44  thf('15', plain,
% 0.20/0.44      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.44         (u1_struct_0 @ sk_A))
% 0.20/0.44        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('16', plain,
% 0.20/0.44      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.20/0.44         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.20/0.44      inference('split', [status(esa)], ['15'])).
% 0.20/0.44  thf('17', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(dt_k1_tex_2, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.20/0.44         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.44       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.20/0.44         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.20/0.44         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.20/0.44  thf('18', plain,
% 0.20/0.44      (![X7 : $i, X8 : $i]:
% 0.20/0.44         (~ (l1_pre_topc @ X7)
% 0.20/0.44          | (v2_struct_0 @ X7)
% 0.20/0.44          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.20/0.44          | (m1_pre_topc @ (k1_tex_2 @ X7 @ X8) @ X7))),
% 0.20/0.44      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.20/0.44  thf('19', plain,
% 0.20/0.44      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.44        | (v2_struct_0 @ sk_A)
% 0.20/0.44        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.44      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.44  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('21', plain,
% 0.20/0.44      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.20/0.44      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.44  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('23', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.44      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.44  thf(cc10_tex_2, axiom,
% 0.20/0.44    (![A:$i]:
% 0.20/0.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.44       ( ![B:$i]:
% 0.20/0.44         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.44           ( ( ~( v2_struct_0 @ B ) ) =>
% 0.20/0.44             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tex_2 @ B @ A ) ) ) ) ) ) ))).
% 0.20/0.44  thf('24', plain,
% 0.20/0.44      (![X3 : $i, X4 : $i]:
% 0.20/0.44         (~ (m1_pre_topc @ X3 @ X4)
% 0.20/0.44          | ~ (v1_tex_2 @ X3 @ X4)
% 0.20/0.44          | (v2_struct_0 @ X3)
% 0.20/0.44          | ~ (l1_pre_topc @ X4)
% 0.20/0.44          | ~ (v7_struct_0 @ X4)
% 0.20/0.44          | (v2_struct_0 @ X4))),
% 0.20/0.44      inference('cnf', [status(esa)], [cc10_tex_2])).
% 0.20/0.44  thf('25', plain,
% 0.20/0.44      (((v2_struct_0 @ sk_A)
% 0.20/0.44        | ~ (v7_struct_0 @ sk_A)
% 0.20/0.44        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.44        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.44        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.44      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.44  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('27', plain,
% 0.20/0.44      (((v2_struct_0 @ sk_A)
% 0.20/0.44        | ~ (v7_struct_0 @ sk_A)
% 0.20/0.44        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.44        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.44      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.44  thf('28', plain,
% 0.20/0.44      ((((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.44         | ~ (v7_struct_0 @ sk_A)
% 0.20/0.44         | (v2_struct_0 @ sk_A)))
% 0.20/0.44         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.20/0.44      inference('sup-', [status(thm)], ['16', '27'])).
% 0.20/0.44  thf('29', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('30', plain,
% 0.20/0.44      (![X7 : $i, X8 : $i]:
% 0.20/0.44         (~ (l1_pre_topc @ X7)
% 0.20/0.44          | (v2_struct_0 @ X7)
% 0.20/0.44          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.20/0.44          | ~ (v2_struct_0 @ (k1_tex_2 @ X7 @ X8)))),
% 0.20/0.44      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.20/0.44  thf('31', plain,
% 0.20/0.44      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.44        | (v2_struct_0 @ sk_A)
% 0.20/0.44        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.44      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.44  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('33', plain,
% 0.20/0.44      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.20/0.44      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.44  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('35', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.20/0.44      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.44  thf('36', plain,
% 0.20/0.44      ((((v2_struct_0 @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 0.20/0.44         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.20/0.44      inference('clc', [status(thm)], ['28', '35'])).
% 0.20/0.44  thf('37', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('38', plain,
% 0.20/0.44      ((~ (v7_struct_0 @ sk_A))
% 0.20/0.44         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.20/0.44      inference('clc', [status(thm)], ['36', '37'])).
% 0.20/0.44  thf('39', plain,
% 0.20/0.44      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.44         (u1_struct_0 @ sk_A))) | 
% 0.20/0.44       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.44      inference('sup-', [status(thm)], ['14', '38'])).
% 0.20/0.44  thf('40', plain,
% 0.20/0.44      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.44         (u1_struct_0 @ sk_A))) | 
% 0.20/0.44       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.44      inference('split', [status(esa)], ['15'])).
% 0.20/0.44  thf('41', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.44      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.44  thf(cc13_tex_2, axiom,
% 0.20/0.44    (![A:$i]:
% 0.20/0.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( ~( v7_struct_0 @ A ) ) & 
% 0.20/0.44         ( l1_pre_topc @ A ) ) =>
% 0.20/0.44       ( ![B:$i]:
% 0.20/0.44         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.44           ( ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tex_2 @ B @ A ) ) ) =>
% 0.20/0.44             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v7_struct_0 @ B ) ) ) ) ) ) ))).
% 0.20/0.44  thf('42', plain,
% 0.20/0.44      (![X5 : $i, X6 : $i]:
% 0.20/0.44         (~ (m1_pre_topc @ X5 @ X6)
% 0.20/0.44          | ~ (v7_struct_0 @ X5)
% 0.20/0.44          | (v1_tex_2 @ X5 @ X6)
% 0.20/0.44          | (v2_struct_0 @ X5)
% 0.20/0.44          | ~ (l1_pre_topc @ X6)
% 0.20/0.44          | (v7_struct_0 @ X6)
% 0.20/0.44          | (v2_struct_0 @ X6))),
% 0.20/0.44      inference('cnf', [status(esa)], [cc13_tex_2])).
% 0.20/0.44  thf('43', plain,
% 0.20/0.44      (((v2_struct_0 @ sk_A)
% 0.20/0.44        | (v7_struct_0 @ sk_A)
% 0.20/0.44        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.44        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.44        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.44        | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)))),
% 0.20/0.44      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.44  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('45', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf(fc2_tex_2, axiom,
% 0.20/0.44    (![A:$i,B:$i]:
% 0.20/0.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.20/0.44         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.44       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.20/0.44         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.20/0.44         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.20/0.44  thf('46', plain,
% 0.20/0.44      (![X9 : $i, X10 : $i]:
% 0.20/0.44         (~ (l1_pre_topc @ X9)
% 0.20/0.44          | (v2_struct_0 @ X9)
% 0.20/0.44          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.20/0.44          | (v7_struct_0 @ (k1_tex_2 @ X9 @ X10)))),
% 0.20/0.44      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.20/0.44  thf('47', plain,
% 0.20/0.44      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.44        | (v2_struct_0 @ sk_A)
% 0.20/0.44        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.44      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.44  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('49', plain,
% 0.20/0.44      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.20/0.44      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.44  thf('50', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('51', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.20/0.44      inference('clc', [status(thm)], ['49', '50'])).
% 0.20/0.44  thf('52', plain,
% 0.20/0.44      (((v2_struct_0 @ sk_A)
% 0.20/0.44        | (v7_struct_0 @ sk_A)
% 0.20/0.44        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.44        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.44      inference('demod', [status(thm)], ['43', '44', '51'])).
% 0.20/0.44  thf('53', plain,
% 0.20/0.44      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))
% 0.20/0.44         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.20/0.44      inference('split', [status(esa)], ['0'])).
% 0.20/0.44  thf('54', plain,
% 0.20/0.44      ((((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))
% 0.20/0.44         | (v7_struct_0 @ sk_A)
% 0.20/0.44         | (v2_struct_0 @ sk_A)))
% 0.20/0.44         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.20/0.44      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.44  thf('55', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B))),
% 0.20/0.44      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.44  thf('56', plain,
% 0.20/0.44      ((((v2_struct_0 @ sk_A) | (v7_struct_0 @ sk_A)))
% 0.20/0.44         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.20/0.44      inference('clc', [status(thm)], ['54', '55'])).
% 0.20/0.44  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('58', plain,
% 0.20/0.44      (((v7_struct_0 @ sk_A))
% 0.20/0.44         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A)))),
% 0.20/0.44      inference('clc', [status(thm)], ['56', '57'])).
% 0.20/0.44  thf('59', plain,
% 0.20/0.44      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.44         (u1_struct_0 @ sk_A)))
% 0.20/0.44         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.44               (u1_struct_0 @ sk_A))))),
% 0.20/0.44      inference('split', [status(esa)], ['15'])).
% 0.20/0.44  thf(t8_tex_2, axiom,
% 0.20/0.44    (![A:$i]:
% 0.20/0.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.44       ( ![B:$i]:
% 0.20/0.44         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.44           ( ~( ( v1_subset_1 @
% 0.20/0.44                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.20/0.44                  ( u1_struct_0 @ A ) ) & 
% 0.20/0.44                ( v7_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.44  thf('60', plain,
% 0.20/0.44      (![X13 : $i, X14 : $i]:
% 0.20/0.44         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.20/0.44          | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X14) @ X13) @ 
% 0.20/0.44               (u1_struct_0 @ X14))
% 0.20/0.44          | ~ (v7_struct_0 @ X14)
% 0.20/0.44          | ~ (l1_struct_0 @ X14)
% 0.20/0.44          | (v2_struct_0 @ X14))),
% 0.20/0.44      inference('cnf', [status(esa)], [t8_tex_2])).
% 0.20/0.44  thf('61', plain,
% 0.20/0.44      ((((v2_struct_0 @ sk_A)
% 0.20/0.44         | ~ (l1_struct_0 @ sk_A)
% 0.20/0.44         | ~ (v7_struct_0 @ sk_A)
% 0.20/0.44         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))
% 0.20/0.44         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.44               (u1_struct_0 @ sk_A))))),
% 0.20/0.44      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.44  thf('62', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.44      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.44  thf('63', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('64', plain,
% 0.20/0.44      ((((v2_struct_0 @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 0.20/0.44         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.44               (u1_struct_0 @ sk_A))))),
% 0.20/0.44      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.20/0.44  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.44  thf('66', plain,
% 0.20/0.44      ((~ (v7_struct_0 @ sk_A))
% 0.20/0.44         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.44               (u1_struct_0 @ sk_A))))),
% 0.20/0.44      inference('clc', [status(thm)], ['64', '65'])).
% 0.20/0.44  thf('67', plain,
% 0.20/0.44      (~
% 0.20/0.44       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.20/0.44         (u1_struct_0 @ sk_A))) | 
% 0.20/0.44       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.44      inference('sup-', [status(thm)], ['58', '66'])).
% 0.20/0.44  thf('68', plain, ($false),
% 0.20/0.44      inference('sat_resolution*', [status(thm)], ['1', '39', '40', '67'])).
% 0.20/0.44  
% 0.20/0.44  % SZS output end Refutation
% 0.20/0.44  
% 0.20/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
