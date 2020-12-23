%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kS1omgjCdb

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:08 EST 2020

% Result     : Theorem 1.04s
% Output     : Refutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :  127 (1468 expanded)
%              Number of leaves         :   30 ( 411 expanded)
%              Depth                    :   25
%              Number of atoms          : 1048 (19045 expanded)
%              Number of equality atoms :   10 (  90 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

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
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
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
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('2',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X32 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X32 @ X33 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('9',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A ),
    inference(clc,[status(thm)],['11','12'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ~ ( v1_subset_1 @ X28 @ X29 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( v1_zfmisc_1 @ X29 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_2])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ) )
    | ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ X43 )
      | ( v1_subset_1 @ ( k6_domain_1 @ X43 @ X42 ) @ X43 )
      | ( v1_zfmisc_1 @ X43 )
      | ( v1_xboole_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t7_tex_2])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t13_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                <=> ( v1_tex_2 @ B @ A ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X37 @ X38 )
      | ( X39
       != ( u1_struct_0 @ X37 ) )
      | ~ ( v1_tex_2 @ X37 @ X38 )
      | ( v1_subset_1 @ X39 @ ( u1_struct_0 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t13_tex_2])).

thf('27',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( l1_pre_topc @ X38 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( v1_tex_2 @ X37 @ X38 )
      | ~ ( m1_pre_topc @ X37 @ X38 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A ),
    inference(clc,[status(thm)],['11','12'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(cc4_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ~ ( v1_subset_1 @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( v1_subset_1 @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc4_subset_1])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['23'])).

thf('40',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('41',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X31 = X30 )
      | ( v1_subset_1 @ X31 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('42',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('44',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_pre_topc @ X37 @ X38 )
      | ( X39
       != ( u1_struct_0 @ X37 ) )
      | ~ ( v1_subset_1 @ X39 @ ( u1_struct_0 @ X38 ) )
      | ( v1_tex_2 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[t13_tex_2])).

thf('45',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( l1_pre_topc @ X38 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X37 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ( v1_tex_2 @ X37 @ X38 )
      | ~ ( v1_subset_1 @ ( u1_struct_0 @ X37 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( m1_pre_topc @ X37 @ X38 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A )
    | ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A ),
    inference(clc,[status(thm)],['11','12'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) )
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf('51',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A ) ),
    inference(split,[status(esa)],['37'])).

thf('52',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) )
              & ( v7_struct_0 @ A ) ) ) ) )).

thf('53',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( u1_struct_0 @ X45 ) )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X45 ) @ X44 ) @ ( u1_struct_0 @ X45 ) )
      | ~ ( v7_struct_0 @ X45 )
      | ~ ( l1_struct_0 @ X45 )
      | ( v2_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t8_tex_2])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ) @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) )
        | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) )
        | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('56',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A ),
    inference(clc,[status(thm)],['11','12'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('57',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('61',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('62',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ) )).

thf('64',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X34 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('65',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','62','69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A )
    | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['23'])).

thf('78',plain,(
    v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A ),
    inference('sat_resolution*',[status(thm)],['38','76','77'])).

thf('79',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['36','78'])).

thf('80',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['22','79'])).

thf('81',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['37'])).

thf('82',plain,(
    ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['38','76'])).

thf('83',plain,(
    ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['81','82'])).

thf('84',plain,(
    v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['80','83'])).

thf('85',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('86',plain,(
    v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) @ sk_A ),
    inference('sat_resolution*',[status(thm)],['38','76','77'])).

thf('87',plain,(
    v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ) ) ),
    inference(demod,[status(thm)],['19','84','87'])).

thf('89',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['36','78'])).

thf('90',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('91',plain,(
    ! [X24: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('92',plain,
    ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) )
    | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('94',plain,(
    v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_3 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    $false ),
    inference(demod,[status(thm)],['6','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kS1omgjCdb
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:29:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.04/1.24  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.04/1.24  % Solved by: fo/fo7.sh
% 1.04/1.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.04/1.24  % done 766 iterations in 0.791s
% 1.04/1.24  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.04/1.24  % SZS output start Refutation
% 1.04/1.24  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 1.04/1.24  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.04/1.24  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.04/1.24  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.04/1.24  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.04/1.24  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 1.04/1.24  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.04/1.24  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 1.04/1.24  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.04/1.24  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 1.04/1.24  thf(sk_A_type, type, sk_A: $i).
% 1.04/1.24  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.04/1.24  thf(sk_B_3_type, type, sk_B_3: $i).
% 1.04/1.24  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 1.04/1.24  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.04/1.24  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.04/1.24  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 1.04/1.24  thf(t20_tex_2, conjecture,
% 1.04/1.24    (![A:$i]:
% 1.04/1.24     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.04/1.24       ( ![B:$i]:
% 1.04/1.24         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.04/1.24           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 1.04/1.24             ( v1_subset_1 @
% 1.04/1.24               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.04/1.24  thf(zf_stmt_0, negated_conjecture,
% 1.04/1.24    (~( ![A:$i]:
% 1.04/1.24        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 1.04/1.24          ( ![B:$i]:
% 1.04/1.24            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.04/1.24              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 1.04/1.24                ( v1_subset_1 @
% 1.04/1.24                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 1.04/1.24                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 1.04/1.24    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 1.04/1.24  thf('0', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf(dt_k1_tex_2, axiom,
% 1.04/1.24    (![A:$i,B:$i]:
% 1.04/1.24     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 1.04/1.24         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 1.04/1.24       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 1.04/1.24         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 1.04/1.24         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 1.04/1.24  thf('1', plain,
% 1.04/1.24      (![X32 : $i, X33 : $i]:
% 1.04/1.24         (~ (l1_pre_topc @ X32)
% 1.04/1.24          | (v2_struct_0 @ X32)
% 1.04/1.24          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 1.04/1.24          | ~ (v2_struct_0 @ (k1_tex_2 @ X32 @ X33)))),
% 1.04/1.24      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 1.04/1.24  thf('2', plain,
% 1.04/1.24      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3))
% 1.04/1.24        | (v2_struct_0 @ sk_A)
% 1.04/1.24        | ~ (l1_pre_topc @ sk_A))),
% 1.04/1.24      inference('sup-', [status(thm)], ['0', '1'])).
% 1.04/1.24  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('4', plain,
% 1.04/1.24      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)) | (v2_struct_0 @ sk_A))),
% 1.04/1.24      inference('demod', [status(thm)], ['2', '3'])).
% 1.04/1.24  thf('5', plain, (~ (v2_struct_0 @ sk_A)),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('6', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3))),
% 1.04/1.24      inference('clc', [status(thm)], ['4', '5'])).
% 1.04/1.24  thf('7', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('8', plain,
% 1.04/1.24      (![X32 : $i, X33 : $i]:
% 1.04/1.24         (~ (l1_pre_topc @ X32)
% 1.04/1.24          | (v2_struct_0 @ X32)
% 1.04/1.24          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X32))
% 1.04/1.24          | (m1_pre_topc @ (k1_tex_2 @ X32 @ X33) @ X32))),
% 1.04/1.24      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 1.04/1.24  thf('9', plain,
% 1.04/1.24      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A)
% 1.04/1.24        | (v2_struct_0 @ sk_A)
% 1.04/1.24        | ~ (l1_pre_topc @ sk_A))),
% 1.04/1.24      inference('sup-', [status(thm)], ['7', '8'])).
% 1.04/1.24  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('11', plain,
% 1.04/1.24      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A)
% 1.04/1.24        | (v2_struct_0 @ sk_A))),
% 1.04/1.24      inference('demod', [status(thm)], ['9', '10'])).
% 1.04/1.24  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('13', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A)),
% 1.04/1.24      inference('clc', [status(thm)], ['11', '12'])).
% 1.04/1.24  thf(t1_tsep_1, axiom,
% 1.04/1.24    (![A:$i]:
% 1.04/1.24     ( ( l1_pre_topc @ A ) =>
% 1.04/1.24       ( ![B:$i]:
% 1.04/1.24         ( ( m1_pre_topc @ B @ A ) =>
% 1.04/1.24           ( m1_subset_1 @
% 1.04/1.24             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.04/1.24  thf('14', plain,
% 1.04/1.24      (![X26 : $i, X27 : $i]:
% 1.04/1.24         (~ (m1_pre_topc @ X26 @ X27)
% 1.04/1.24          | (m1_subset_1 @ (u1_struct_0 @ X26) @ 
% 1.04/1.24             (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.04/1.24          | ~ (l1_pre_topc @ X27))),
% 1.04/1.24      inference('cnf', [status(esa)], [t1_tsep_1])).
% 1.04/1.24  thf('15', plain,
% 1.04/1.24      ((~ (l1_pre_topc @ sk_A)
% 1.04/1.24        | (m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)) @ 
% 1.04/1.24           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.04/1.24      inference('sup-', [status(thm)], ['13', '14'])).
% 1.04/1.24  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('17', plain,
% 1.04/1.24      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)) @ 
% 1.04/1.24        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.04/1.24      inference('demod', [status(thm)], ['15', '16'])).
% 1.04/1.24  thf(cc2_tex_2, axiom,
% 1.04/1.24    (![A:$i]:
% 1.04/1.24     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 1.04/1.24       ( ![B:$i]:
% 1.04/1.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.04/1.24           ( ( ~( v1_xboole_0 @ B ) ) => ( ~( v1_subset_1 @ B @ A ) ) ) ) ) ))).
% 1.04/1.24  thf('18', plain,
% 1.04/1.24      (![X28 : $i, X29 : $i]:
% 1.04/1.24         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 1.04/1.24          | ~ (v1_subset_1 @ X28 @ X29)
% 1.04/1.24          | (v1_xboole_0 @ X28)
% 1.04/1.24          | ~ (v1_zfmisc_1 @ X29)
% 1.04/1.24          | (v1_xboole_0 @ X29))),
% 1.04/1.24      inference('cnf', [status(esa)], [cc2_tex_2])).
% 1.04/1.24  thf('19', plain,
% 1.04/1.24      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.04/1.24        | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 1.04/1.24        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)))
% 1.04/1.24        | ~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)) @ 
% 1.04/1.24             (u1_struct_0 @ sk_A)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['17', '18'])).
% 1.04/1.24  thf('20', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf(t7_tex_2, axiom,
% 1.04/1.24    (![A:$i]:
% 1.04/1.24     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_zfmisc_1 @ A ) ) ) =>
% 1.04/1.24       ( ![B:$i]:
% 1.04/1.24         ( ( m1_subset_1 @ B @ A ) =>
% 1.04/1.24           ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) ))).
% 1.04/1.24  thf('21', plain,
% 1.04/1.24      (![X42 : $i, X43 : $i]:
% 1.04/1.24         (~ (m1_subset_1 @ X42 @ X43)
% 1.04/1.24          | (v1_subset_1 @ (k6_domain_1 @ X43 @ X42) @ X43)
% 1.04/1.24          | (v1_zfmisc_1 @ X43)
% 1.04/1.24          | (v1_xboole_0 @ X43))),
% 1.04/1.24      inference('cnf', [status(esa)], [t7_tex_2])).
% 1.04/1.24  thf('22', plain,
% 1.04/1.24      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.04/1.24        | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 1.04/1.24        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_3) @ 
% 1.04/1.24           (u1_struct_0 @ sk_A)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['20', '21'])).
% 1.04/1.24  thf('23', plain,
% 1.04/1.24      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_3) @ 
% 1.04/1.24         (u1_struct_0 @ sk_A))
% 1.04/1.24        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('24', plain,
% 1.04/1.24      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A))
% 1.04/1.24         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A)))),
% 1.04/1.24      inference('split', [status(esa)], ['23'])).
% 1.04/1.24  thf('25', plain,
% 1.04/1.24      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)) @ 
% 1.04/1.24        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.04/1.24      inference('demod', [status(thm)], ['15', '16'])).
% 1.04/1.24  thf(t13_tex_2, axiom,
% 1.04/1.24    (![A:$i]:
% 1.04/1.24     ( ( l1_pre_topc @ A ) =>
% 1.04/1.24       ( ![B:$i]:
% 1.04/1.24         ( ( m1_pre_topc @ B @ A ) =>
% 1.04/1.24           ( ![C:$i]:
% 1.04/1.24             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.04/1.24               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 1.04/1.24                 ( ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) <=>
% 1.04/1.24                   ( v1_tex_2 @ B @ A ) ) ) ) ) ) ) ))).
% 1.04/1.24  thf('26', plain,
% 1.04/1.24      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.04/1.24         (~ (m1_pre_topc @ X37 @ X38)
% 1.04/1.24          | ((X39) != (u1_struct_0 @ X37))
% 1.04/1.24          | ~ (v1_tex_2 @ X37 @ X38)
% 1.04/1.24          | (v1_subset_1 @ X39 @ (u1_struct_0 @ X38))
% 1.04/1.24          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 1.04/1.24          | ~ (l1_pre_topc @ X38))),
% 1.04/1.24      inference('cnf', [status(esa)], [t13_tex_2])).
% 1.04/1.24  thf('27', plain,
% 1.04/1.24      (![X37 : $i, X38 : $i]:
% 1.04/1.24         (~ (l1_pre_topc @ X38)
% 1.04/1.24          | ~ (m1_subset_1 @ (u1_struct_0 @ X37) @ 
% 1.04/1.24               (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 1.04/1.24          | (v1_subset_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X38))
% 1.04/1.24          | ~ (v1_tex_2 @ X37 @ X38)
% 1.04/1.24          | ~ (m1_pre_topc @ X37 @ X38))),
% 1.04/1.24      inference('simplify', [status(thm)], ['26'])).
% 1.04/1.24  thf('28', plain,
% 1.04/1.24      ((~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A)
% 1.04/1.24        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A)
% 1.04/1.24        | (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)) @ 
% 1.04/1.24           (u1_struct_0 @ sk_A))
% 1.04/1.24        | ~ (l1_pre_topc @ sk_A))),
% 1.04/1.24      inference('sup-', [status(thm)], ['25', '27'])).
% 1.04/1.24  thf('29', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A)),
% 1.04/1.24      inference('clc', [status(thm)], ['11', '12'])).
% 1.04/1.24  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('31', plain,
% 1.04/1.24      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A)
% 1.04/1.24        | (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)) @ 
% 1.04/1.24           (u1_struct_0 @ sk_A)))),
% 1.04/1.24      inference('demod', [status(thm)], ['28', '29', '30'])).
% 1.04/1.24  thf('32', plain,
% 1.04/1.24      (((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)) @ 
% 1.04/1.24         (u1_struct_0 @ sk_A)))
% 1.04/1.24         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['24', '31'])).
% 1.04/1.24  thf('33', plain,
% 1.04/1.24      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)) @ 
% 1.04/1.24        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.04/1.24      inference('demod', [status(thm)], ['15', '16'])).
% 1.04/1.24  thf(cc4_subset_1, axiom,
% 1.04/1.24    (![A:$i]:
% 1.04/1.24     ( ( v1_xboole_0 @ A ) =>
% 1.04/1.24       ( ![B:$i]:
% 1.04/1.24         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.04/1.24           ( ~( v1_subset_1 @ B @ A ) ) ) ) ))).
% 1.04/1.24  thf('34', plain,
% 1.04/1.24      (![X13 : $i, X14 : $i]:
% 1.04/1.24         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 1.04/1.24          | ~ (v1_subset_1 @ X13 @ X14)
% 1.04/1.24          | ~ (v1_xboole_0 @ X14))),
% 1.04/1.24      inference('cnf', [status(esa)], [cc4_subset_1])).
% 1.04/1.24  thf('35', plain,
% 1.04/1.24      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.04/1.24        | ~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)) @ 
% 1.04/1.24             (u1_struct_0 @ sk_A)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['33', '34'])).
% 1.04/1.24  thf('36', plain,
% 1.04/1.24      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 1.04/1.24         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['32', '35'])).
% 1.04/1.24  thf('37', plain,
% 1.04/1.24      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_3) @ 
% 1.04/1.24           (u1_struct_0 @ sk_A))
% 1.04/1.24        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('38', plain,
% 1.04/1.24      (~
% 1.04/1.24       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_3) @ 
% 1.04/1.24         (u1_struct_0 @ sk_A))) | 
% 1.04/1.24       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A))),
% 1.04/1.24      inference('split', [status(esa)], ['37'])).
% 1.04/1.24  thf('39', plain,
% 1.04/1.24      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_3) @ 
% 1.04/1.24         (u1_struct_0 @ sk_A)))
% 1.04/1.24         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_3) @ 
% 1.04/1.24               (u1_struct_0 @ sk_A))))),
% 1.04/1.24      inference('split', [status(esa)], ['23'])).
% 1.04/1.24  thf('40', plain,
% 1.04/1.24      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)) @ 
% 1.04/1.24        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.04/1.24      inference('demod', [status(thm)], ['15', '16'])).
% 1.04/1.24  thf(d7_subset_1, axiom,
% 1.04/1.24    (![A:$i,B:$i]:
% 1.04/1.24     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.04/1.24       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 1.04/1.24  thf('41', plain,
% 1.04/1.24      (![X30 : $i, X31 : $i]:
% 1.04/1.24         (((X31) = (X30))
% 1.04/1.24          | (v1_subset_1 @ X31 @ X30)
% 1.04/1.24          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 1.04/1.24      inference('cnf', [status(esa)], [d7_subset_1])).
% 1.04/1.24  thf('42', plain,
% 1.04/1.24      (((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)) @ 
% 1.04/1.24         (u1_struct_0 @ sk_A))
% 1.04/1.24        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)) = (u1_struct_0 @ sk_A)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['40', '41'])).
% 1.04/1.24  thf('43', plain,
% 1.04/1.24      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)) @ 
% 1.04/1.24        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.04/1.24      inference('demod', [status(thm)], ['15', '16'])).
% 1.04/1.24  thf('44', plain,
% 1.04/1.24      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.04/1.24         (~ (m1_pre_topc @ X37 @ X38)
% 1.04/1.24          | ((X39) != (u1_struct_0 @ X37))
% 1.04/1.24          | ~ (v1_subset_1 @ X39 @ (u1_struct_0 @ X38))
% 1.04/1.24          | (v1_tex_2 @ X37 @ X38)
% 1.04/1.24          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 1.04/1.24          | ~ (l1_pre_topc @ X38))),
% 1.04/1.24      inference('cnf', [status(esa)], [t13_tex_2])).
% 1.04/1.24  thf('45', plain,
% 1.04/1.24      (![X37 : $i, X38 : $i]:
% 1.04/1.24         (~ (l1_pre_topc @ X38)
% 1.04/1.24          | ~ (m1_subset_1 @ (u1_struct_0 @ X37) @ 
% 1.04/1.24               (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 1.04/1.24          | (v1_tex_2 @ X37 @ X38)
% 1.04/1.24          | ~ (v1_subset_1 @ (u1_struct_0 @ X37) @ (u1_struct_0 @ X38))
% 1.04/1.24          | ~ (m1_pre_topc @ X37 @ X38))),
% 1.04/1.24      inference('simplify', [status(thm)], ['44'])).
% 1.04/1.24  thf('46', plain,
% 1.04/1.24      ((~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A)
% 1.04/1.24        | ~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)) @ 
% 1.04/1.24             (u1_struct_0 @ sk_A))
% 1.04/1.24        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A)
% 1.04/1.24        | ~ (l1_pre_topc @ sk_A))),
% 1.04/1.24      inference('sup-', [status(thm)], ['43', '45'])).
% 1.04/1.24  thf('47', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A)),
% 1.04/1.24      inference('clc', [status(thm)], ['11', '12'])).
% 1.04/1.24  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('49', plain,
% 1.04/1.24      ((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)) @ 
% 1.04/1.24           (u1_struct_0 @ sk_A))
% 1.04/1.24        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A))),
% 1.04/1.24      inference('demod', [status(thm)], ['46', '47', '48'])).
% 1.04/1.24  thf('50', plain,
% 1.04/1.24      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)) = (u1_struct_0 @ sk_A))
% 1.04/1.24        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A))),
% 1.04/1.24      inference('sup-', [status(thm)], ['42', '49'])).
% 1.04/1.24  thf('51', plain,
% 1.04/1.24      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A))
% 1.04/1.24         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A)))),
% 1.04/1.24      inference('split', [status(esa)], ['37'])).
% 1.04/1.24  thf('52', plain,
% 1.04/1.24      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)) = (u1_struct_0 @ sk_A)))
% 1.04/1.24         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['50', '51'])).
% 1.04/1.24  thf(t8_tex_2, axiom,
% 1.04/1.24    (![A:$i]:
% 1.04/1.24     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.04/1.24       ( ![B:$i]:
% 1.04/1.24         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.04/1.24           ( ~( ( v1_subset_1 @
% 1.04/1.24                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 1.04/1.24                  ( u1_struct_0 @ A ) ) & 
% 1.04/1.24                ( v7_struct_0 @ A ) ) ) ) ) ))).
% 1.04/1.24  thf('53', plain,
% 1.04/1.24      (![X44 : $i, X45 : $i]:
% 1.04/1.24         (~ (m1_subset_1 @ X44 @ (u1_struct_0 @ X45))
% 1.04/1.24          | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X45) @ X44) @ 
% 1.04/1.24               (u1_struct_0 @ X45))
% 1.04/1.24          | ~ (v7_struct_0 @ X45)
% 1.04/1.24          | ~ (l1_struct_0 @ X45)
% 1.04/1.24          | (v2_struct_0 @ X45))),
% 1.04/1.24      inference('cnf', [status(esa)], [t8_tex_2])).
% 1.04/1.24  thf('54', plain,
% 1.04/1.24      ((![X0 : $i]:
% 1.04/1.24          (~ (v1_subset_1 @ 
% 1.04/1.24              (k6_domain_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)) @ X0) @ 
% 1.04/1.24              (u1_struct_0 @ sk_A))
% 1.04/1.24           | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3))
% 1.04/1.24           | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3))
% 1.04/1.24           | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3))
% 1.04/1.24           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)))))
% 1.04/1.24         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['52', '53'])).
% 1.04/1.24  thf('55', plain,
% 1.04/1.24      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)) = (u1_struct_0 @ sk_A)))
% 1.04/1.24         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['50', '51'])).
% 1.04/1.24  thf('56', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A)),
% 1.04/1.24      inference('clc', [status(thm)], ['11', '12'])).
% 1.04/1.24  thf(dt_m1_pre_topc, axiom,
% 1.04/1.24    (![A:$i]:
% 1.04/1.24     ( ( l1_pre_topc @ A ) =>
% 1.04/1.24       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 1.04/1.24  thf('57', plain,
% 1.04/1.24      (![X21 : $i, X22 : $i]:
% 1.04/1.24         (~ (m1_pre_topc @ X21 @ X22)
% 1.04/1.24          | (l1_pre_topc @ X21)
% 1.04/1.24          | ~ (l1_pre_topc @ X22))),
% 1.04/1.24      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 1.04/1.24  thf('58', plain,
% 1.04/1.24      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_3)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['56', '57'])).
% 1.04/1.24  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('60', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_3))),
% 1.04/1.24      inference('demod', [status(thm)], ['58', '59'])).
% 1.04/1.24  thf(dt_l1_pre_topc, axiom,
% 1.04/1.24    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.04/1.24  thf('61', plain,
% 1.04/1.24      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 1.04/1.24      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.04/1.24  thf('62', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3))),
% 1.04/1.24      inference('sup-', [status(thm)], ['60', '61'])).
% 1.04/1.24  thf('63', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf(fc2_tex_2, axiom,
% 1.04/1.24    (![A:$i,B:$i]:
% 1.04/1.24     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 1.04/1.24         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 1.04/1.24       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 1.04/1.24         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 1.04/1.24         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 1.04/1.24  thf('64', plain,
% 1.04/1.24      (![X34 : $i, X35 : $i]:
% 1.04/1.24         (~ (l1_pre_topc @ X34)
% 1.04/1.24          | (v2_struct_0 @ X34)
% 1.04/1.24          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X34))
% 1.04/1.24          | (v7_struct_0 @ (k1_tex_2 @ X34 @ X35)))),
% 1.04/1.24      inference('cnf', [status(esa)], [fc2_tex_2])).
% 1.04/1.24  thf('65', plain,
% 1.04/1.24      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3))
% 1.04/1.24        | (v2_struct_0 @ sk_A)
% 1.04/1.24        | ~ (l1_pre_topc @ sk_A))),
% 1.04/1.24      inference('sup-', [status(thm)], ['63', '64'])).
% 1.04/1.24  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('67', plain,
% 1.04/1.24      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)) | (v2_struct_0 @ sk_A))),
% 1.04/1.24      inference('demod', [status(thm)], ['65', '66'])).
% 1.04/1.24  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('69', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3))),
% 1.04/1.24      inference('clc', [status(thm)], ['67', '68'])).
% 1.04/1.24  thf('70', plain,
% 1.04/1.24      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)) = (u1_struct_0 @ sk_A)))
% 1.04/1.24         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['50', '51'])).
% 1.04/1.24  thf('71', plain,
% 1.04/1.24      ((![X0 : $i]:
% 1.04/1.24          (~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 1.04/1.24              (u1_struct_0 @ sk_A))
% 1.04/1.24           | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3))
% 1.04/1.24           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 1.04/1.24         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A)))),
% 1.04/1.24      inference('demod', [status(thm)], ['54', '55', '62', '69', '70'])).
% 1.04/1.24  thf('72', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3))),
% 1.04/1.24      inference('clc', [status(thm)], ['4', '5'])).
% 1.04/1.24  thf('73', plain,
% 1.04/1.24      ((![X0 : $i]:
% 1.04/1.24          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 1.04/1.24           | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 1.04/1.24                (u1_struct_0 @ sk_A))))
% 1.04/1.24         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A)))),
% 1.04/1.24      inference('clc', [status(thm)], ['71', '72'])).
% 1.04/1.24  thf('74', plain,
% 1.04/1.24      ((~ (m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A)))
% 1.04/1.24         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A)) & 
% 1.04/1.24             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_3) @ 
% 1.04/1.24               (u1_struct_0 @ sk_A))))),
% 1.04/1.24      inference('sup-', [status(thm)], ['39', '73'])).
% 1.04/1.24  thf('75', plain, ((m1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 1.04/1.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.04/1.24  thf('76', plain,
% 1.04/1.24      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A)) | 
% 1.04/1.24       ~
% 1.04/1.24       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_3) @ 
% 1.04/1.24         (u1_struct_0 @ sk_A)))),
% 1.04/1.24      inference('demod', [status(thm)], ['74', '75'])).
% 1.04/1.24  thf('77', plain,
% 1.04/1.24      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A)) | 
% 1.04/1.24       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_3) @ 
% 1.04/1.24         (u1_struct_0 @ sk_A)))),
% 1.04/1.24      inference('split', [status(esa)], ['23'])).
% 1.04/1.24  thf('78', plain, (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A))),
% 1.04/1.24      inference('sat_resolution*', [status(thm)], ['38', '76', '77'])).
% 1.04/1.24  thf('79', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 1.04/1.24      inference('simpl_trail', [status(thm)], ['36', '78'])).
% 1.04/1.24  thf('80', plain,
% 1.04/1.24      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_3) @ 
% 1.04/1.24         (u1_struct_0 @ sk_A))
% 1.04/1.24        | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.04/1.24      inference('clc', [status(thm)], ['22', '79'])).
% 1.04/1.24  thf('81', plain,
% 1.04/1.24      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_3) @ 
% 1.04/1.24           (u1_struct_0 @ sk_A)))
% 1.04/1.24         <= (~
% 1.04/1.24             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_3) @ 
% 1.04/1.24               (u1_struct_0 @ sk_A))))),
% 1.04/1.24      inference('split', [status(esa)], ['37'])).
% 1.04/1.24  thf('82', plain,
% 1.04/1.24      (~
% 1.04/1.24       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_3) @ 
% 1.04/1.24         (u1_struct_0 @ sk_A)))),
% 1.04/1.24      inference('sat_resolution*', [status(thm)], ['38', '76'])).
% 1.04/1.24  thf('83', plain,
% 1.04/1.24      (~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_3) @ 
% 1.04/1.24          (u1_struct_0 @ sk_A))),
% 1.04/1.24      inference('simpl_trail', [status(thm)], ['81', '82'])).
% 1.04/1.24  thf('84', plain, ((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))),
% 1.04/1.24      inference('clc', [status(thm)], ['80', '83'])).
% 1.04/1.24  thf('85', plain,
% 1.04/1.24      (((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)) @ 
% 1.04/1.24         (u1_struct_0 @ sk_A)))
% 1.04/1.24         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['24', '31'])).
% 1.04/1.24  thf('86', plain, (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_3) @ sk_A))),
% 1.04/1.24      inference('sat_resolution*', [status(thm)], ['38', '76', '77'])).
% 1.04/1.24  thf('87', plain,
% 1.04/1.24      ((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)) @ 
% 1.04/1.24        (u1_struct_0 @ sk_A))),
% 1.04/1.24      inference('simpl_trail', [status(thm)], ['85', '86'])).
% 1.04/1.24  thf('88', plain,
% 1.04/1.24      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.04/1.24        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3))))),
% 1.04/1.24      inference('demod', [status(thm)], ['19', '84', '87'])).
% 1.04/1.24  thf('89', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 1.04/1.24      inference('simpl_trail', [status(thm)], ['36', '78'])).
% 1.04/1.24  thf('90', plain,
% 1.04/1.24      ((v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)))),
% 1.04/1.24      inference('clc', [status(thm)], ['88', '89'])).
% 1.04/1.24  thf(fc2_struct_0, axiom,
% 1.04/1.24    (![A:$i]:
% 1.04/1.24     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.04/1.24       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.04/1.24  thf('91', plain,
% 1.04/1.24      (![X24 : $i]:
% 1.04/1.24         (~ (v1_xboole_0 @ (u1_struct_0 @ X24))
% 1.04/1.24          | ~ (l1_struct_0 @ X24)
% 1.04/1.24          | (v2_struct_0 @ X24))),
% 1.04/1.24      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.04/1.24  thf('92', plain,
% 1.04/1.24      (((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3))
% 1.04/1.24        | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3)))),
% 1.04/1.24      inference('sup-', [status(thm)], ['90', '91'])).
% 1.04/1.24  thf('93', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3))),
% 1.04/1.24      inference('sup-', [status(thm)], ['60', '61'])).
% 1.04/1.24  thf('94', plain, ((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_3))),
% 1.04/1.24      inference('demod', [status(thm)], ['92', '93'])).
% 1.04/1.24  thf('95', plain, ($false), inference('demod', [status(thm)], ['6', '94'])).
% 1.04/1.24  
% 1.04/1.24  % SZS output end Refutation
% 1.04/1.24  
% 1.04/1.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
