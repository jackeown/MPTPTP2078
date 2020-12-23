%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fjiRssmTfM

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 328 expanded)
%              Number of leaves         :   33 ( 103 expanded)
%              Depth                    :   19
%              Number of atoms          : 1133 (3967 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

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
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X34 @ X35 )
      | ( v1_subset_1 @ ( k6_domain_1 @ X35 @ X34 ) @ X35 )
      | ( v1_zfmisc_1 @ X35 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t7_tex_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(cc2_realset1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X17: $i] :
      ( ( v1_zfmisc_1 @ X17 )
      | ~ ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc2_realset1])).

thf('6',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) )
        & ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X25 @ X26 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('13',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference(clc,[status(thm)],['15','16'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

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

thf('22',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( v1_tex_2 @ X20 @ X21 )
      | ( X22
       != ( u1_struct_0 @ X20 ) )
      | ( v1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('23',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_tex_2 @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference(clc,[status(thm)],['15','16'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','27'])).

thf('29',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(cc2_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ~ ( v1_xboole_0 @ B )
           => ~ ( v1_subset_1 @ B @ A ) ) ) ) )).

thf('30',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( v1_subset_1 @ X18 @ X19 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( v1_zfmisc_1 @ X19 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_2])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) )
    | ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) )
      | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(clc,[status(thm)],['32','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) )
   <= ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
      & ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','36'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('38',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('39',plain,
    ( ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
      | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) )
   <= ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
      & ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference(clc,[status(thm)],['15','16'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('41',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('42',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('45',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('46',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
   <= ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
      & ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('50',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('57',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('58',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X24 = X23 )
      | ( v1_subset_1 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('59',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference(clc,[status(thm)],['15','16'])).

thf('61',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( ( sk_C @ X20 @ X21 )
        = ( u1_struct_0 @ X20 ) )
      | ( v1_tex_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( v1_subset_1 @ ( sk_C @ X20 @ X21 ) @ ( u1_struct_0 @ X21 ) )
      | ( v1_tex_2 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('68',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ),
    inference(clc,[status(thm)],['15','16'])).

thf('71',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('73',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['59','73'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('75',plain,(
    ! [X14: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ~ ( v7_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('76',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
      | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ) )).

thf('78',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('79',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('85',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['76','83','84'])).

thf('86',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf(t6_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
              & ( v1_zfmisc_1 @ A ) ) ) ) )).

thf('87',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ X33 )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ X33 @ X32 ) @ X33 )
      | ~ ( v1_zfmisc_1 @ X33 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t6_tex_2])).

thf('88',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('92',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('93',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('96',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['93','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','55','56','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fjiRssmTfM
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:45:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 122 iterations in 0.068s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.53  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.20/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.53  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.20/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.53  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.20/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.53  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.20/0.53  thf(t20_tex_2, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.20/0.53             ( v1_subset_1 @
% 0.20/0.53               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.20/0.53                ( v1_subset_1 @
% 0.20/0.53                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.20/0.53                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.20/0.53           (u1_struct_0 @ sk_A))
% 0.20/0.53        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (~
% 0.20/0.53       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.20/0.53         (u1_struct_0 @ sk_A))) | 
% 0.20/0.53       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('2', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t7_tex_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ A ) =>
% 0.20/0.53           ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X34 : $i, X35 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X34 @ X35)
% 0.20/0.53          | (v1_subset_1 @ (k6_domain_1 @ X35 @ X34) @ X35)
% 0.20/0.53          | (v1_zfmisc_1 @ X35)
% 0.20/0.53          | (v1_xboole_0 @ X35))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_tex_2])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.20/0.53           (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf(cc2_realset1, axiom,
% 0.20/0.53    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_zfmisc_1 @ A ) ))).
% 0.20/0.53  thf('5', plain, (![X17 : $i]: ((v1_zfmisc_1 @ X17) | ~ (v1_xboole_0 @ X17))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc2_realset1])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.20/0.53         (u1_struct_0 @ sk_A))
% 0.20/0.53        | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('clc', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.20/0.53           (u1_struct_0 @ sk_A)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.20/0.53         (u1_struct_0 @ sk_A))
% 0.20/0.53        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))
% 0.20/0.53         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['9'])).
% 0.20/0.53  thf('11', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(dt_k1_tex_2, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.20/0.53         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.20/0.53         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.20/0.53         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X25 : $i, X26 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X25)
% 0.20/0.53          | (v2_struct_0 @ X25)
% 0.20/0.53          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 0.20/0.53          | (m1_pre_topc @ (k1_tex_2 @ X25 @ X26) @ X25))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.20/0.53        | (v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.53  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.20/0.53        | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('17', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)),
% 0.20/0.53      inference('clc', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf(t1_tsep_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.53           ( m1_subset_1 @
% 0.20/0.53             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X15 @ X16)
% 0.20/0.53          | (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.20/0.53          | ~ (l1_pre_topc @ X16))),
% 0.20/0.53      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | (m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) @ 
% 0.20/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.53  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf(d3_tex_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.53           ( ( v1_tex_2 @ B @ A ) <=>
% 0.20/0.53             ( ![C:$i]:
% 0.20/0.53               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.53                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X20 @ X21)
% 0.20/0.53          | ~ (v1_tex_2 @ X20 @ X21)
% 0.20/0.53          | ((X22) != (u1_struct_0 @ X20))
% 0.20/0.53          | (v1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 0.20/0.53          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.53          | ~ (l1_pre_topc @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X21)
% 0.20/0.53          | ~ (m1_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.20/0.53               (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.20/0.53          | (v1_subset_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X21))
% 0.20/0.53          | ~ (v1_tex_2 @ X20 @ X21)
% 0.20/0.53          | ~ (m1_pre_topc @ X20 @ X21))),
% 0.20/0.53      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      ((~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.20/0.53        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.20/0.53        | (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) @ 
% 0.20/0.53           (u1_struct_0 @ sk_A))
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['21', '23'])).
% 0.20/0.53  thf('25', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)),
% 0.20/0.53      inference('clc', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.20/0.53        | (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) @ 
% 0.20/0.53           (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) @ 
% 0.20/0.53         (u1_struct_0 @ sk_A)))
% 0.20/0.53         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['10', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf(cc2_tex_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53           ( ( ~( v1_xboole_0 @ B ) ) => ( ~( v1_subset_1 @ B @ A ) ) ) ) ) ))).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.20/0.53          | ~ (v1_subset_1 @ X18 @ X19)
% 0.20/0.53          | (v1_xboole_0 @ X18)
% 0.20/0.53          | ~ (v1_zfmisc_1 @ X19)
% 0.20/0.53          | (v1_xboole_0 @ X19))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc2_tex_2])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)))
% 0.20/0.53        | ~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) @ 
% 0.20/0.53             (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      ((((v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)))
% 0.20/0.53         | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.53         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['28', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf(cc1_subset_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_xboole_0 @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.20/0.53          | (v1_xboole_0 @ X2)
% 0.20/0.53          | ~ (v1_xboole_0 @ X3))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (((~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.53         | (v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)))))
% 0.20/0.53         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.20/0.53      inference('clc', [status(thm)], ['32', '35'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))) & 
% 0.20/0.53             ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['8', '36'])).
% 0.20/0.53  thf(fc2_struct_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.53       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (![X13 : $i]:
% 0.20/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X13))
% 0.20/0.53          | ~ (l1_struct_0 @ X13)
% 0.20/0.53          | (v2_struct_0 @ X13))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      ((((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))
% 0.20/0.53         | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))) & 
% 0.20/0.53             ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf('40', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)),
% 0.20/0.53      inference('clc', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf(dt_m1_pre_topc, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X11 @ X12)
% 0.20/0.53          | (l1_pre_topc @ X11)
% 0.20/0.53          | ~ (l1_pre_topc @ X12))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.53  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('44', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2))),
% 0.20/0.53      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.53  thf(dt_l1_pre_topc, axiom,
% 0.20/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.53  thf('46', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))),
% 0.20/0.53      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))) & 
% 0.20/0.53             ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['39', '46'])).
% 0.20/0.53  thf('48', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (![X25 : $i, X26 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X25)
% 0.20/0.53          | (v2_struct_0 @ X25)
% 0.20/0.53          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 0.20/0.53          | ~ (v2_struct_0 @ (k1_tex_2 @ X25 @ X26)))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))
% 0.20/0.53        | (v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.53  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.53  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('54', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))),
% 0.20/0.53      inference('clc', [status(thm)], ['52', '53'])).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.20/0.53         (u1_struct_0 @ sk_A))) | 
% 0.20/0.53       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['47', '54'])).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.20/0.53         (u1_struct_0 @ sk_A))) | 
% 0.20/0.53       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))),
% 0.20/0.53      inference('split', [status(esa)], ['9'])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) @ 
% 0.20/0.53        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf(d7_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.20/0.53  thf('58', plain,
% 0.20/0.53      (![X23 : $i, X24 : $i]:
% 0.20/0.53         (((X24) = (X23))
% 0.20/0.53          | (v1_subset_1 @ X24 @ X23)
% 0.20/0.53          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X23)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.20/0.53  thf('59', plain,
% 0.20/0.53      (((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) @ 
% 0.20/0.53         (u1_struct_0 @ sk_A))
% 0.20/0.53        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) = (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.53  thf('60', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)),
% 0.20/0.53      inference('clc', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X20 @ X21)
% 0.20/0.53          | ((sk_C @ X20 @ X21) = (u1_struct_0 @ X20))
% 0.20/0.53          | (v1_tex_2 @ X20 @ X21)
% 0.20/0.53          | ~ (l1_pre_topc @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.20/0.53  thf('62', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.20/0.53        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.20/0.53            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.53  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('64', plain,
% 0.20/0.53      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.20/0.53        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.20/0.53            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))))),
% 0.20/0.53      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.53  thf('65', plain,
% 0.20/0.53      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('66', plain,
% 0.20/0.53      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.20/0.53          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['64', '65'])).
% 0.20/0.53  thf('67', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X20 @ X21)
% 0.20/0.53          | ~ (v1_subset_1 @ (sk_C @ X20 @ X21) @ (u1_struct_0 @ X21))
% 0.20/0.53          | (v1_tex_2 @ X20 @ X21)
% 0.20/0.53          | ~ (l1_pre_topc @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.20/0.53  thf('68', plain,
% 0.20/0.53      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) @ 
% 0.20/0.53            (u1_struct_0 @ sk_A))
% 0.20/0.53         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)
% 0.20/0.53         | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['66', '67'])).
% 0.20/0.53  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('70', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)),
% 0.20/0.53      inference('clc', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('71', plain,
% 0.20/0.53      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) @ 
% 0.20/0.53            (u1_struct_0 @ sk_A))
% 0.20/0.53         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.20/0.53  thf('72', plain,
% 0.20/0.53      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('73', plain,
% 0.20/0.53      ((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) @ 
% 0.20/0.53           (u1_struct_0 @ sk_A)))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.20/0.53      inference('clc', [status(thm)], ['71', '72'])).
% 0.20/0.53  thf('74', plain,
% 0.20/0.53      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) = (u1_struct_0 @ sk_A)))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['59', '73'])).
% 0.20/0.53  thf(fc7_struct_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.53       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.53  thf('75', plain,
% 0.20/0.53      (![X14 : $i]:
% 0.20/0.53         ((v1_zfmisc_1 @ (u1_struct_0 @ X14))
% 0.20/0.53          | ~ (l1_struct_0 @ X14)
% 0.20/0.53          | ~ (v7_struct_0 @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.20/0.53  thf('76', plain,
% 0.20/0.53      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.53         | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))
% 0.20/0.53         | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['74', '75'])).
% 0.20/0.53  thf('77', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(fc2_tex_2, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.20/0.53         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.20/0.53         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.20/0.53         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.20/0.53  thf('78', plain,
% 0.20/0.53      (![X27 : $i, X28 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X27)
% 0.20/0.53          | (v2_struct_0 @ X27)
% 0.20/0.53          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 0.20/0.53          | (v7_struct_0 @ (k1_tex_2 @ X27 @ X28)))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.20/0.53  thf('79', plain,
% 0.20/0.53      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))
% 0.20/0.53        | (v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['77', '78'])).
% 0.20/0.53  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('81', plain,
% 0.20/0.53      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2)) | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['79', '80'])).
% 0.20/0.53  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('83', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))),
% 0.20/0.53      inference('clc', [status(thm)], ['81', '82'])).
% 0.20/0.53  thf('84', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_2))),
% 0.20/0.53      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.53  thf('85', plain,
% 0.20/0.53      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['76', '83', '84'])).
% 0.20/0.53  thf('86', plain,
% 0.20/0.53      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.20/0.53         (u1_struct_0 @ sk_A)))
% 0.20/0.53         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['9'])).
% 0.20/0.53  thf(t6_tex_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ A ) =>
% 0.20/0.53           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.20/0.53                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.20/0.53  thf('87', plain,
% 0.20/0.53      (![X32 : $i, X33 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X32 @ X33)
% 0.20/0.53          | ~ (v1_subset_1 @ (k6_domain_1 @ X33 @ X32) @ X33)
% 0.20/0.53          | ~ (v1_zfmisc_1 @ X33)
% 0.20/0.53          | (v1_xboole_0 @ X33))),
% 0.20/0.53      inference('cnf', [status(esa)], [t6_tex_2])).
% 0.20/0.53  thf('88', plain,
% 0.20/0.53      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53         | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.53         | ~ (m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))))
% 0.20/0.53         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['86', '87'])).
% 0.20/0.53  thf('89', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('90', plain,
% 0.20/0.53      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53         | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.53         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['88', '89'])).
% 0.20/0.53  thf('91', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)) & 
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['85', '90'])).
% 0.20/0.53  thf('92', plain,
% 0.20/0.53      (![X13 : $i]:
% 0.20/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X13))
% 0.20/0.53          | ~ (l1_struct_0 @ X13)
% 0.20/0.53          | (v2_struct_0 @ X13))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.53  thf('93', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)) & 
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['91', '92'])).
% 0.20/0.53  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('95', plain,
% 0.20/0.53      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.53  thf('96', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.53      inference('sup-', [status(thm)], ['94', '95'])).
% 0.20/0.53  thf('97', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A)) & 
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['93', '96'])).
% 0.20/0.53  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('99', plain,
% 0.20/0.53      (~
% 0.20/0.53       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) @ 
% 0.20/0.53         (u1_struct_0 @ sk_A))) | 
% 0.20/0.53       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_2) @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['97', '98'])).
% 0.20/0.53  thf('100', plain, ($false),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['1', '55', '56', '99'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
