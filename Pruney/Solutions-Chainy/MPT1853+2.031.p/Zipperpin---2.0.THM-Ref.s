%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zB5Ul4st7G

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:06 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 854 expanded)
%              Number of leaves         :   36 ( 251 expanded)
%              Depth                    :   24
%              Number of atoms          : 1391 (10406 expanded)
%              Number of equality atoms :   14 (  58 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(o_2_0_pre_topc_type,type,(
    o_2_0_pre_topc: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

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
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X29 @ X30 ) ) ) ),
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
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X29 @ X30 ) @ X29 ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
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

thf(cc1_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ( v1_subset_1 @ B @ A )
           => ( v1_xboole_0 @ B ) ) ) ) )).

thf('18',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( v1_xboole_0 @ X22 )
      | ~ ( v1_subset_1 @ X22 @ X23 )
      | ~ ( v1_zfmisc_1 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc1_tex_2])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ X36 )
      | ( v1_subset_1 @ ( k6_domain_1 @ X36 @ X35 ) @ X36 )
      | ( v1_zfmisc_1 @ X36 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t7_tex_2])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('26',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('27',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('29',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('30',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['23'])).

thf('35',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('36',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X28 = X27 )
      | ( v1_subset_1 @ X28 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('37',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
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

thf('39',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( ( sk_C @ X24 @ X25 )
        = ( u1_struct_0 @ X24 ) )
      | ( v1_tex_2 @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['23'])).

thf('44',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( v1_subset_1 @ ( sk_C @ X24 @ X25 ) @ ( u1_struct_0 @ X25 ) )
      | ( v1_tex_2 @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('46',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['11','12'])).

thf('49',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['23'])).

thf('51',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['37','51'])).

thf(rc3_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ~ ( v1_subset_1 @ B @ A )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('53',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ ( sk_B @ X2 ) @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('54',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ ( sk_B @ X2 ) @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('55',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X28 = X27 )
      | ( v1_subset_1 @ X28 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ ( sk_B @ X0 ) @ X0 )
      | ( ( sk_B @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X2: $i] :
      ~ ( v1_subset_1 @ ( sk_B @ X2 ) @ X2 ) ),
    inference(cnf,[status(esa)],[rc3_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( sk_B @ X0 )
      = X0 ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['53','58'])).

thf(dt_o_2_0_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( o_2_0_pre_topc @ A @ B ) @ B ) ) )).

thf('60',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( m1_subset_1 @ ( o_2_0_pre_topc @ X11 @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_o_2_0_pre_topc])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( o_2_0_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( o_2_0_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('63',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ X36 )
      | ( v1_subset_1 @ ( k6_domain_1 @ X36 @ X35 ) @ X36 )
      | ( v1_zfmisc_1 @ X36 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t7_tex_2])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_zfmisc_1 @ ( u1_struct_0 @ X0 ) )
      | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( o_2_0_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(t8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) )
              & ( v7_struct_0 @ A ) ) ) ) )).

thf('65',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X38 ) )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X38 ) @ X37 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( v7_struct_0 @ X38 )
      | ~ ( l1_struct_0 @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t8_tex_2])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ ( o_2_0_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_zfmisc_1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['52','71'])).

thf('73',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['11','12'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('74',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( l1_pre_topc @ X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('75',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
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

thf('79',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X31 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('80',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('86',plain,(
    ! [X8: $i] :
      ( ( l1_struct_0 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('87',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['72','77','84','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('90',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['91'])).

thf(t6_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
              & ( v1_zfmisc_1 @ A ) ) ) ) )).

thf('93',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ X34 )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ X34 @ X33 ) @ X34 )
      | ~ ( v1_zfmisc_1 @ X34 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t6_tex_2])).

thf('94',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['90','96'])).

thf('98',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['37','51'])).

thf('99',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('100',plain,
    ( ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('102',plain,
    ( ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('104',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','104'])).

thf('106',plain,(
    ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['34','105'])).

thf('107',plain,(
    v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['33','106'])).

thf('108',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['91'])).

thf('109',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('110',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( v1_tex_2 @ X24 @ X25 )
      | ( X26
       != ( u1_struct_0 @ X24 ) )
      | ( v1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('111',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( v1_tex_2 @ X24 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X25 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['109','111'])).

thf('113',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['11','12'])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['108','115'])).

thf('117',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['91'])).

thf('118',plain,(
    v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference('sat_resolution*',[status(thm)],['34','105','117'])).

thf('119',plain,(
    v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['116','118'])).

thf('120',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['19','107','119'])).

thf('121',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('123',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['120','123'])).

thf('125',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('126',plain,
    ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('128',plain,(
    v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    $false ),
    inference(demod,[status(thm)],['6','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zB5Ul4st7G
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:26:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.39/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.56  % Solved by: fo/fo7.sh
% 0.39/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.56  % done 175 iterations in 0.098s
% 0.39/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.56  % SZS output start Refutation
% 0.39/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.39/0.56  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.39/0.56  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.39/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.56  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.39/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.56  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.39/0.56  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.39/0.56  thf(o_2_0_pre_topc_type, type, o_2_0_pre_topc: $i > $i > $i).
% 0.39/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.56  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.39/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.39/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.39/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.56  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.39/0.56  thf(t20_tex_2, conjecture,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.56           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.39/0.56             ( v1_subset_1 @
% 0.39/0.56               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.39/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.56    (~( ![A:$i]:
% 0.39/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.56          ( ![B:$i]:
% 0.39/0.56            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.56              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.39/0.56                ( v1_subset_1 @
% 0.39/0.56                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.39/0.56                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.39/0.56    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.39/0.56  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(dt_k1_tex_2, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.39/0.56         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.56       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.39/0.56         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.39/0.56         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.39/0.56  thf('1', plain,
% 0.39/0.56      (![X29 : $i, X30 : $i]:
% 0.39/0.56         (~ (l1_pre_topc @ X29)
% 0.39/0.56          | (v2_struct_0 @ X29)
% 0.39/0.56          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 0.39/0.56          | ~ (v2_struct_0 @ (k1_tex_2 @ X29 @ X30)))),
% 0.39/0.56      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.39/0.56  thf('2', plain,
% 0.39/0.56      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.39/0.56        | (v2_struct_0 @ sk_A)
% 0.39/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.39/0.56  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('4', plain,
% 0.39/0.56      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.39/0.56      inference('demod', [status(thm)], ['2', '3'])).
% 0.39/0.56  thf('5', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('6', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.39/0.56      inference('clc', [status(thm)], ['4', '5'])).
% 0.39/0.56  thf('7', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('8', plain,
% 0.39/0.56      (![X29 : $i, X30 : $i]:
% 0.39/0.56         (~ (l1_pre_topc @ X29)
% 0.39/0.56          | (v2_struct_0 @ X29)
% 0.39/0.56          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 0.39/0.56          | (m1_pre_topc @ (k1_tex_2 @ X29 @ X30) @ X29))),
% 0.39/0.56      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.39/0.56  thf('9', plain,
% 0.39/0.56      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.39/0.56        | (v2_struct_0 @ sk_A)
% 0.39/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.56  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('11', plain,
% 0.39/0.56      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.39/0.56        | (v2_struct_0 @ sk_A))),
% 0.39/0.56      inference('demod', [status(thm)], ['9', '10'])).
% 0.39/0.56  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('13', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.39/0.56      inference('clc', [status(thm)], ['11', '12'])).
% 0.39/0.56  thf(t1_tsep_1, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( l1_pre_topc @ A ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.39/0.56           ( m1_subset_1 @
% 0.39/0.56             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.39/0.56  thf('14', plain,
% 0.39/0.56      (![X19 : $i, X20 : $i]:
% 0.39/0.56         (~ (m1_pre_topc @ X19 @ X20)
% 0.39/0.56          | (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.39/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.39/0.56          | ~ (l1_pre_topc @ X20))),
% 0.39/0.56      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.39/0.56  thf('15', plain,
% 0.39/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.56        | (m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.39/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.39/0.56  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('17', plain,
% 0.39/0.56      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.39/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.39/0.56  thf(cc1_tex_2, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.56           ( ( v1_subset_1 @ B @ A ) => ( v1_xboole_0 @ B ) ) ) ) ))).
% 0.39/0.56  thf('18', plain,
% 0.39/0.56      (![X22 : $i, X23 : $i]:
% 0.39/0.56         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.39/0.56          | (v1_xboole_0 @ X22)
% 0.39/0.56          | ~ (v1_subset_1 @ X22 @ X23)
% 0.39/0.56          | ~ (v1_zfmisc_1 @ X23)
% 0.39/0.56          | (v1_xboole_0 @ X23))),
% 0.39/0.56      inference('cnf', [status(esa)], [cc1_tex_2])).
% 0.39/0.56  thf('19', plain,
% 0.39/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56        | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.39/0.56        | ~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.39/0.56             (u1_struct_0 @ sk_A))
% 0.39/0.56        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.39/0.56  thf('20', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(t7_tex_2, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_zfmisc_1 @ A ) ) ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( m1_subset_1 @ B @ A ) =>
% 0.39/0.56           ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) ))).
% 0.39/0.56  thf('21', plain,
% 0.39/0.56      (![X35 : $i, X36 : $i]:
% 0.39/0.56         (~ (m1_subset_1 @ X35 @ X36)
% 0.39/0.56          | (v1_subset_1 @ (k6_domain_1 @ X36 @ X35) @ X36)
% 0.39/0.56          | (v1_zfmisc_1 @ X36)
% 0.39/0.56          | (v1_xboole_0 @ X36))),
% 0.39/0.56      inference('cnf', [status(esa)], [t7_tex_2])).
% 0.39/0.56  thf('22', plain,
% 0.39/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56        | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.39/0.56        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56           (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.39/0.56  thf('23', plain,
% 0.39/0.56      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56           (u1_struct_0 @ sk_A))
% 0.39/0.56        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('24', plain,
% 0.39/0.56      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56           (u1_struct_0 @ sk_A)))
% 0.39/0.56         <= (~
% 0.39/0.56             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56               (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('split', [status(esa)], ['23'])).
% 0.39/0.56  thf('25', plain,
% 0.39/0.56      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.39/0.56         <= (~
% 0.39/0.56             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56               (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['22', '24'])).
% 0.39/0.56  thf(fc2_struct_0, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.39/0.56       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.39/0.56  thf('26', plain,
% 0.39/0.56      (![X13 : $i]:
% 0.39/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X13))
% 0.39/0.56          | ~ (l1_struct_0 @ X13)
% 0.39/0.56          | (v2_struct_0 @ X13))),
% 0.39/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.39/0.56  thf('27', plain,
% 0.39/0.56      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | ~ (l1_struct_0 @ sk_A)))
% 0.39/0.56         <= (~
% 0.39/0.56             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56               (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.39/0.56  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(dt_l1_pre_topc, axiom,
% 0.39/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.39/0.56  thf('29', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.39/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.56  thf('30', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.39/0.56  thf('31', plain,
% 0.39/0.56      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.39/0.56         <= (~
% 0.39/0.56             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56               (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('demod', [status(thm)], ['27', '30'])).
% 0.39/0.56  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('33', plain,
% 0.39/0.56      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.56         <= (~
% 0.39/0.56             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56               (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('clc', [status(thm)], ['31', '32'])).
% 0.39/0.56  thf('34', plain,
% 0.39/0.56      (~
% 0.39/0.56       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56         (u1_struct_0 @ sk_A))) | 
% 0.39/0.56       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.39/0.56      inference('split', [status(esa)], ['23'])).
% 0.39/0.56  thf('35', plain,
% 0.39/0.56      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.39/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.39/0.56  thf(d7_subset_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.56       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.39/0.56  thf('36', plain,
% 0.39/0.56      (![X27 : $i, X28 : $i]:
% 0.39/0.56         (((X28) = (X27))
% 0.39/0.56          | (v1_subset_1 @ X28 @ X27)
% 0.39/0.56          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 0.39/0.56      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.39/0.56  thf('37', plain,
% 0.39/0.56      (((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.39/0.56         (u1_struct_0 @ sk_A))
% 0.39/0.56        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.39/0.56  thf('38', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.39/0.56      inference('clc', [status(thm)], ['11', '12'])).
% 0.39/0.56  thf(d3_tex_2, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( l1_pre_topc @ A ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.39/0.56           ( ( v1_tex_2 @ B @ A ) <=>
% 0.39/0.56             ( ![C:$i]:
% 0.39/0.56               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.56                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.39/0.56                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.39/0.56  thf('39', plain,
% 0.39/0.56      (![X24 : $i, X25 : $i]:
% 0.39/0.56         (~ (m1_pre_topc @ X24 @ X25)
% 0.39/0.56          | ((sk_C @ X24 @ X25) = (u1_struct_0 @ X24))
% 0.39/0.56          | (v1_tex_2 @ X24 @ X25)
% 0.39/0.56          | ~ (l1_pre_topc @ X25))),
% 0.39/0.56      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.39/0.56  thf('40', plain,
% 0.39/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.56        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.39/0.56        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.39/0.56            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.39/0.56  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('42', plain,
% 0.39/0.56      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.39/0.56        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.39/0.56            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.39/0.56      inference('demod', [status(thm)], ['40', '41'])).
% 0.39/0.56  thf('43', plain,
% 0.39/0.56      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.39/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.39/0.56      inference('split', [status(esa)], ['23'])).
% 0.39/0.56  thf('44', plain,
% 0.39/0.56      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.39/0.56          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.39/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.39/0.56  thf('45', plain,
% 0.39/0.56      (![X24 : $i, X25 : $i]:
% 0.39/0.56         (~ (m1_pre_topc @ X24 @ X25)
% 0.39/0.56          | ~ (v1_subset_1 @ (sk_C @ X24 @ X25) @ (u1_struct_0 @ X25))
% 0.39/0.56          | (v1_tex_2 @ X24 @ X25)
% 0.39/0.56          | ~ (l1_pre_topc @ X25))),
% 0.39/0.56      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.39/0.56  thf('46', plain,
% 0.39/0.56      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.39/0.56            (u1_struct_0 @ sk_A))
% 0.39/0.56         | ~ (l1_pre_topc @ sk_A)
% 0.39/0.56         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.39/0.56         | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))
% 0.39/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['44', '45'])).
% 0.39/0.56  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('48', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.39/0.56      inference('clc', [status(thm)], ['11', '12'])).
% 0.39/0.56  thf('49', plain,
% 0.39/0.56      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.39/0.56            (u1_struct_0 @ sk_A))
% 0.39/0.56         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))
% 0.39/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.39/0.56      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.39/0.56  thf('50', plain,
% 0.39/0.56      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.39/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.39/0.56      inference('split', [status(esa)], ['23'])).
% 0.39/0.56  thf('51', plain,
% 0.39/0.56      ((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.39/0.56           (u1_struct_0 @ sk_A)))
% 0.39/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.39/0.56      inference('clc', [status(thm)], ['49', '50'])).
% 0.39/0.56  thf('52', plain,
% 0.39/0.56      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))
% 0.39/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['37', '51'])).
% 0.39/0.56  thf(rc3_subset_1, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ?[B:$i]:
% 0.39/0.56       ( ( ~( v1_subset_1 @ B @ A ) ) & 
% 0.39/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.39/0.56  thf('53', plain,
% 0.39/0.56      (![X2 : $i]: (m1_subset_1 @ (sk_B @ X2) @ (k1_zfmisc_1 @ X2))),
% 0.39/0.56      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.39/0.56  thf('54', plain,
% 0.39/0.56      (![X2 : $i]: (m1_subset_1 @ (sk_B @ X2) @ (k1_zfmisc_1 @ X2))),
% 0.39/0.56      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.39/0.56  thf('55', plain,
% 0.39/0.56      (![X27 : $i, X28 : $i]:
% 0.39/0.56         (((X28) = (X27))
% 0.39/0.56          | (v1_subset_1 @ X28 @ X27)
% 0.39/0.56          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 0.39/0.56      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.39/0.56  thf('56', plain,
% 0.39/0.56      (![X0 : $i]: ((v1_subset_1 @ (sk_B @ X0) @ X0) | ((sk_B @ X0) = (X0)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['54', '55'])).
% 0.39/0.56  thf('57', plain, (![X2 : $i]: ~ (v1_subset_1 @ (sk_B @ X2) @ X2)),
% 0.39/0.56      inference('cnf', [status(esa)], [rc3_subset_1])).
% 0.39/0.56  thf('58', plain, (![X0 : $i]: ((sk_B @ X0) = (X0))),
% 0.39/0.56      inference('clc', [status(thm)], ['56', '57'])).
% 0.39/0.56  thf('59', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 0.39/0.56      inference('demod', [status(thm)], ['53', '58'])).
% 0.39/0.56  thf(dt_o_2_0_pre_topc, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( ( l1_pre_topc @ A ) & 
% 0.39/0.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.56       ( m1_subset_1 @ ( o_2_0_pre_topc @ A @ B ) @ B ) ))).
% 0.39/0.56  thf('60', plain,
% 0.39/0.56      (![X11 : $i, X12 : $i]:
% 0.39/0.56         (~ (l1_pre_topc @ X11)
% 0.39/0.56          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.39/0.56          | (m1_subset_1 @ (o_2_0_pre_topc @ X11 @ X12) @ X12))),
% 0.39/0.56      inference('cnf', [status(esa)], [dt_o_2_0_pre_topc])).
% 0.39/0.56  thf('61', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((m1_subset_1 @ (o_2_0_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.39/0.56           (u1_struct_0 @ X0))
% 0.39/0.56          | ~ (l1_pre_topc @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['59', '60'])).
% 0.39/0.56  thf('62', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((m1_subset_1 @ (o_2_0_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.39/0.56           (u1_struct_0 @ X0))
% 0.39/0.56          | ~ (l1_pre_topc @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['59', '60'])).
% 0.39/0.56  thf('63', plain,
% 0.39/0.56      (![X35 : $i, X36 : $i]:
% 0.39/0.56         (~ (m1_subset_1 @ X35 @ X36)
% 0.39/0.56          | (v1_subset_1 @ (k6_domain_1 @ X36 @ X35) @ X36)
% 0.39/0.56          | (v1_zfmisc_1 @ X36)
% 0.39/0.56          | (v1_xboole_0 @ X36))),
% 0.39/0.56      inference('cnf', [status(esa)], [t7_tex_2])).
% 0.39/0.56  thf('64', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (~ (l1_pre_topc @ X0)
% 0.39/0.56          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.39/0.56          | (v1_zfmisc_1 @ (u1_struct_0 @ X0))
% 0.39/0.56          | (v1_subset_1 @ 
% 0.39/0.56             (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 0.39/0.56              (o_2_0_pre_topc @ X0 @ (u1_struct_0 @ X0))) @ 
% 0.39/0.56             (u1_struct_0 @ X0)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['62', '63'])).
% 0.39/0.56  thf(t8_tex_2, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.56           ( ~( ( v1_subset_1 @
% 0.39/0.56                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.39/0.56                  ( u1_struct_0 @ A ) ) & 
% 0.39/0.56                ( v7_struct_0 @ A ) ) ) ) ) ))).
% 0.39/0.56  thf('65', plain,
% 0.39/0.56      (![X37 : $i, X38 : $i]:
% 0.39/0.56         (~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X38))
% 0.39/0.56          | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X38) @ X37) @ 
% 0.39/0.56               (u1_struct_0 @ X38))
% 0.39/0.56          | ~ (v7_struct_0 @ X38)
% 0.39/0.56          | ~ (l1_struct_0 @ X38)
% 0.39/0.56          | (v2_struct_0 @ X38))),
% 0.39/0.56      inference('cnf', [status(esa)], [t8_tex_2])).
% 0.39/0.56  thf('66', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((v1_zfmisc_1 @ (u1_struct_0 @ X0))
% 0.39/0.56          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.39/0.56          | ~ (l1_pre_topc @ X0)
% 0.39/0.56          | (v2_struct_0 @ X0)
% 0.39/0.56          | ~ (l1_struct_0 @ X0)
% 0.39/0.56          | ~ (v7_struct_0 @ X0)
% 0.39/0.56          | ~ (m1_subset_1 @ (o_2_0_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.39/0.56               (u1_struct_0 @ X0)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['64', '65'])).
% 0.39/0.56  thf('67', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (~ (l1_pre_topc @ X0)
% 0.39/0.56          | ~ (v7_struct_0 @ X0)
% 0.39/0.56          | ~ (l1_struct_0 @ X0)
% 0.39/0.56          | (v2_struct_0 @ X0)
% 0.39/0.56          | ~ (l1_pre_topc @ X0)
% 0.39/0.56          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.39/0.56          | (v1_zfmisc_1 @ (u1_struct_0 @ X0)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['61', '66'])).
% 0.39/0.56  thf('68', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((v1_zfmisc_1 @ (u1_struct_0 @ X0))
% 0.39/0.56          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.39/0.56          | (v2_struct_0 @ X0)
% 0.39/0.56          | ~ (l1_struct_0 @ X0)
% 0.39/0.56          | ~ (v7_struct_0 @ X0)
% 0.39/0.56          | ~ (l1_pre_topc @ X0))),
% 0.39/0.56      inference('simplify', [status(thm)], ['67'])).
% 0.39/0.56  thf('69', plain,
% 0.39/0.56      (![X13 : $i]:
% 0.39/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X13))
% 0.39/0.56          | ~ (l1_struct_0 @ X13)
% 0.39/0.56          | (v2_struct_0 @ X13))),
% 0.39/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.39/0.56  thf('70', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (~ (l1_pre_topc @ X0)
% 0.39/0.56          | ~ (v7_struct_0 @ X0)
% 0.39/0.56          | ~ (l1_struct_0 @ X0)
% 0.39/0.56          | (v2_struct_0 @ X0)
% 0.39/0.56          | (v1_zfmisc_1 @ (u1_struct_0 @ X0))
% 0.39/0.56          | (v2_struct_0 @ X0)
% 0.39/0.56          | ~ (l1_struct_0 @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['68', '69'])).
% 0.39/0.56  thf('71', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         ((v1_zfmisc_1 @ (u1_struct_0 @ X0))
% 0.39/0.56          | (v2_struct_0 @ X0)
% 0.39/0.56          | ~ (l1_struct_0 @ X0)
% 0.39/0.56          | ~ (v7_struct_0 @ X0)
% 0.39/0.56          | ~ (l1_pre_topc @ X0))),
% 0.39/0.56      inference('simplify', [status(thm)], ['70'])).
% 0.39/0.56  thf('72', plain,
% 0.39/0.56      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | ~ (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.39/0.56         | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.39/0.56         | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.39/0.56         | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.39/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.39/0.56      inference('sup+', [status(thm)], ['52', '71'])).
% 0.39/0.56  thf('73', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.39/0.56      inference('clc', [status(thm)], ['11', '12'])).
% 0.39/0.56  thf(dt_m1_pre_topc, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( l1_pre_topc @ A ) =>
% 0.39/0.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.39/0.56  thf('74', plain,
% 0.39/0.56      (![X9 : $i, X10 : $i]:
% 0.39/0.56         (~ (m1_pre_topc @ X9 @ X10)
% 0.39/0.56          | (l1_pre_topc @ X9)
% 0.39/0.56          | ~ (l1_pre_topc @ X10))),
% 0.39/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.39/0.56  thf('75', plain,
% 0.39/0.56      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['73', '74'])).
% 0.39/0.56  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('77', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.39/0.56      inference('demod', [status(thm)], ['75', '76'])).
% 0.39/0.56  thf('78', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(fc2_tex_2, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.39/0.56         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.56       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.39/0.56         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.39/0.56         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.39/0.56  thf('79', plain,
% 0.39/0.56      (![X31 : $i, X32 : $i]:
% 0.39/0.56         (~ (l1_pre_topc @ X31)
% 0.39/0.56          | (v2_struct_0 @ X31)
% 0.39/0.56          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X31))
% 0.39/0.56          | (v7_struct_0 @ (k1_tex_2 @ X31 @ X32)))),
% 0.39/0.56      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.39/0.56  thf('80', plain,
% 0.39/0.56      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.39/0.56        | (v2_struct_0 @ sk_A)
% 0.39/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['78', '79'])).
% 0.39/0.56  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('82', plain,
% 0.39/0.56      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.39/0.56      inference('demod', [status(thm)], ['80', '81'])).
% 0.39/0.56  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('84', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.39/0.56      inference('clc', [status(thm)], ['82', '83'])).
% 0.39/0.56  thf('85', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.39/0.56      inference('demod', [status(thm)], ['75', '76'])).
% 0.39/0.56  thf('86', plain, (![X8 : $i]: ((l1_struct_0 @ X8) | ~ (l1_pre_topc @ X8))),
% 0.39/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.56  thf('87', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.39/0.56      inference('sup-', [status(thm)], ['85', '86'])).
% 0.39/0.56  thf('88', plain,
% 0.39/0.56      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.39/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.39/0.56      inference('demod', [status(thm)], ['72', '77', '84', '87'])).
% 0.39/0.56  thf('89', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.39/0.56      inference('clc', [status(thm)], ['4', '5'])).
% 0.39/0.56  thf('90', plain,
% 0.39/0.56      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.39/0.56      inference('clc', [status(thm)], ['88', '89'])).
% 0.39/0.56  thf('91', plain,
% 0.39/0.56      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56         (u1_struct_0 @ sk_A))
% 0.39/0.56        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('92', plain,
% 0.39/0.56      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56         (u1_struct_0 @ sk_A)))
% 0.39/0.56         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56               (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('split', [status(esa)], ['91'])).
% 0.39/0.56  thf(t6_tex_2, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( m1_subset_1 @ B @ A ) =>
% 0.39/0.56           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.39/0.56                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.39/0.56  thf('93', plain,
% 0.39/0.56      (![X33 : $i, X34 : $i]:
% 0.39/0.56         (~ (m1_subset_1 @ X33 @ X34)
% 0.39/0.56          | ~ (v1_subset_1 @ (k6_domain_1 @ X34 @ X33) @ X34)
% 0.39/0.56          | ~ (v1_zfmisc_1 @ X34)
% 0.39/0.56          | (v1_xboole_0 @ X34))),
% 0.39/0.56      inference('cnf', [status(esa)], [t6_tex_2])).
% 0.39/0.56  thf('94', plain,
% 0.39/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.39/0.56         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56               (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['92', '93'])).
% 0.39/0.56  thf('95', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('96', plain,
% 0.39/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.39/0.56         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56               (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('demod', [status(thm)], ['94', '95'])).
% 0.39/0.56  thf('97', plain,
% 0.39/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.39/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) & 
% 0.39/0.56             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56               (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['90', '96'])).
% 0.39/0.56  thf('98', plain,
% 0.39/0.56      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))
% 0.39/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['37', '51'])).
% 0.39/0.56  thf('99', plain,
% 0.39/0.56      (![X13 : $i]:
% 0.39/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X13))
% 0.39/0.56          | ~ (l1_struct_0 @ X13)
% 0.39/0.56          | (v2_struct_0 @ X13))),
% 0.39/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.39/0.56  thf('100', plain,
% 0.39/0.56      (((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.39/0.56         | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.39/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['98', '99'])).
% 0.39/0.56  thf('101', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.39/0.56      inference('sup-', [status(thm)], ['85', '86'])).
% 0.39/0.56  thf('102', plain,
% 0.39/0.56      (((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.39/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.39/0.56      inference('demod', [status(thm)], ['100', '101'])).
% 0.39/0.56  thf('103', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.39/0.56      inference('clc', [status(thm)], ['4', '5'])).
% 0.39/0.56  thf('104', plain,
% 0.39/0.56      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.39/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.39/0.56      inference('clc', [status(thm)], ['102', '103'])).
% 0.39/0.56  thf('105', plain,
% 0.39/0.56      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) | 
% 0.39/0.56       ~
% 0.39/0.56       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56         (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['97', '104'])).
% 0.39/0.56  thf('106', plain,
% 0.39/0.56      (~
% 0.39/0.56       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56         (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('sat_resolution*', [status(thm)], ['34', '105'])).
% 0.39/0.56  thf('107', plain, ((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.56      inference('simpl_trail', [status(thm)], ['33', '106'])).
% 0.39/0.56  thf('108', plain,
% 0.39/0.56      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.39/0.56         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.39/0.56      inference('split', [status(esa)], ['91'])).
% 0.39/0.56  thf('109', plain,
% 0.39/0.56      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.39/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.39/0.56  thf('110', plain,
% 0.39/0.56      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.39/0.56         (~ (m1_pre_topc @ X24 @ X25)
% 0.39/0.56          | ~ (v1_tex_2 @ X24 @ X25)
% 0.39/0.56          | ((X26) != (u1_struct_0 @ X24))
% 0.39/0.56          | (v1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 0.39/0.56          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.39/0.56          | ~ (l1_pre_topc @ X25))),
% 0.39/0.56      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.39/0.56  thf('111', plain,
% 0.39/0.56      (![X24 : $i, X25 : $i]:
% 0.39/0.56         (~ (l1_pre_topc @ X25)
% 0.39/0.56          | ~ (m1_subset_1 @ (u1_struct_0 @ X24) @ 
% 0.39/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.39/0.56          | (v1_subset_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X25))
% 0.39/0.56          | ~ (v1_tex_2 @ X24 @ X25)
% 0.39/0.56          | ~ (m1_pre_topc @ X24 @ X25))),
% 0.39/0.56      inference('simplify', [status(thm)], ['110'])).
% 0.39/0.56  thf('112', plain,
% 0.39/0.56      ((~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.39/0.56        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.39/0.56        | (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.39/0.56           (u1_struct_0 @ sk_A))
% 0.39/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['109', '111'])).
% 0.39/0.56  thf('113', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.39/0.56      inference('clc', [status(thm)], ['11', '12'])).
% 0.39/0.56  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('115', plain,
% 0.39/0.56      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.39/0.56        | (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.39/0.56           (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('demod', [status(thm)], ['112', '113', '114'])).
% 0.39/0.56  thf('116', plain,
% 0.39/0.56      (((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.39/0.56         (u1_struct_0 @ sk_A)))
% 0.39/0.56         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['108', '115'])).
% 0.39/0.56  thf('117', plain,
% 0.39/0.56      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) | 
% 0.39/0.56       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56         (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('split', [status(esa)], ['91'])).
% 0.39/0.56  thf('118', plain, (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.39/0.56      inference('sat_resolution*', [status(thm)], ['34', '105', '117'])).
% 0.39/0.56  thf('119', plain,
% 0.39/0.56      ((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.39/0.56        (u1_struct_0 @ sk_A))),
% 0.39/0.56      inference('simpl_trail', [status(thm)], ['116', '118'])).
% 0.39/0.56  thf('120', plain,
% 0.39/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.39/0.56      inference('demod', [status(thm)], ['19', '107', '119'])).
% 0.39/0.56  thf('121', plain,
% 0.39/0.56      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.39/0.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.39/0.56  thf(cc1_subset_1, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( v1_xboole_0 @ A ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.39/0.56  thf('122', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i]:
% 0.39/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.39/0.56          | (v1_xboole_0 @ X0)
% 0.39/0.56          | ~ (v1_xboole_0 @ X1))),
% 0.39/0.56      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.39/0.56  thf('123', plain,
% 0.39/0.56      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['121', '122'])).
% 0.39/0.56  thf('124', plain,
% 0.39/0.56      ((v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.39/0.56      inference('clc', [status(thm)], ['120', '123'])).
% 0.39/0.56  thf('125', plain,
% 0.39/0.56      (![X13 : $i]:
% 0.39/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X13))
% 0.39/0.56          | ~ (l1_struct_0 @ X13)
% 0.39/0.56          | (v2_struct_0 @ X13))),
% 0.39/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.39/0.56  thf('126', plain,
% 0.39/0.56      (((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.39/0.56        | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['124', '125'])).
% 0.39/0.56  thf('127', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.39/0.56      inference('sup-', [status(thm)], ['85', '86'])).
% 0.39/0.56  thf('128', plain, ((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.39/0.56      inference('demod', [status(thm)], ['126', '127'])).
% 0.39/0.56  thf('129', plain, ($false), inference('demod', [status(thm)], ['6', '128'])).
% 0.39/0.56  
% 0.39/0.56  % SZS output end Refutation
% 0.39/0.56  
% 0.41/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
