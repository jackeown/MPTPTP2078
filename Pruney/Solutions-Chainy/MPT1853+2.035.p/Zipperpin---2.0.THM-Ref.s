%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q1IbSfJwVw

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:07 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 712 expanded)
%              Number of leaves         :   35 ( 208 expanded)
%              Depth                    :   24
%              Number of atoms          : 1232 (8797 expanded)
%              Number of equality atoms :   17 (  42 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X22 @ X23 ) ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X22 @ X23 ) @ X22 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( v1_subset_1 @ X13 @ X14 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( v1_zfmisc_1 @ X14 )
      | ( v1_xboole_0 @ X14 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ X9 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ( X21 = X20 )
      | ( v1_subset_1 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ( X15
       != ( k6_domain_1 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( v1_zfmisc_1 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
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

thf(cc1_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_zfmisc_1 @ A ) ) )).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v1_zfmisc_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_zfmisc_1])).

thf('34',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['25'])).

thf('36',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('37',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X21 = X20 )
      | ( v1_subset_1 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('38',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
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

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( ( sk_C @ X17 @ X18 )
        = ( u1_struct_0 @ X17 ) )
      | ( v1_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['25'])).

thf('45',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( v1_subset_1 @ ( sk_C @ X17 @ X18 ) @ ( u1_struct_0 @ X18 ) )
      | ( v1_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('47',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['11','12'])).

thf('50',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['25'])).

thf('52',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['38','52'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('54',plain,(
    ! [X8: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ~ ( v7_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('55',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
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

thf('57',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('58',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['11','12'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('64',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( l1_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('65',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('68',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('69',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['55','62','69'])).

thf(fc6_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('71',plain,(
    ! [X7: $i] :
      ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ( v7_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_struct_0])).

thf('72',plain,
    ( ( ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('75',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v7_struct_0 @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('77',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['77'])).

thf(t8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) )
              & ( v7_struct_0 @ A ) ) ) ) )).

thf('79',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X27 ) @ X26 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v7_struct_0 @ X27 )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t8_tex_2])).

thf('80',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['73','74'])).

thf('82',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','85'])).

thf('87',plain,(
    ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['35','86'])).

thf('88',plain,(
    v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['34','87'])).

thf('89',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['77'])).

thf('90',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('91',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( v1_tex_2 @ X17 @ X18 )
      | ( X19
       != ( u1_struct_0 @ X17 ) )
      | ( v1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('92',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( v1_tex_2 @ X17 @ X18 )
      | ~ ( m1_pre_topc @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['90','92'])).

thf('94',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['11','12'])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['89','96'])).

thf('98',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['77'])).

thf('99',plain,(
    v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference('sat_resolution*',[status(thm)],['35','86','98'])).

thf('100',plain,(
    v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['97','99'])).

thf('101',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['19','88','100'])).

thf('102',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['89','96'])).

thf('103',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(cc4_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ~ ( v1_subset_1 @ B @ A ) ) ) )).

thf('104',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( v1_subset_1 @ X1 @ X2 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc4_subset_1])).

thf('105',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,(
    v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference('sat_resolution*',[status(thm)],['35','86','98'])).

thf('108',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['106','107'])).

thf('109',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['101','108'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('110',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('111',plain,
    ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('113',plain,(
    v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    $false ),
    inference(demod,[status(thm)],['6','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.q1IbSfJwVw
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 196 iterations in 0.127s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.38/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.58  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.38/0.58  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.38/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.58  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.38/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.38/0.58  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.38/0.58  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.38/0.58  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.38/0.58  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.38/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.38/0.58  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.38/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.38/0.58  thf(t20_tex_2, conjecture,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.58           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.38/0.58             ( v1_subset_1 @
% 0.38/0.58               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.38/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.58    (~( ![A:$i]:
% 0.38/0.58        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.38/0.58          ( ![B:$i]:
% 0.38/0.58            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.58              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.38/0.58                ( v1_subset_1 @
% 0.38/0.58                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.38/0.58                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.38/0.58    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.38/0.58  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(dt_k1_tex_2, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.38/0.58         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.58       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.38/0.58         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.38/0.58         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.38/0.58  thf('1', plain,
% 0.38/0.58      (![X22 : $i, X23 : $i]:
% 0.38/0.58         (~ (l1_pre_topc @ X22)
% 0.38/0.58          | (v2_struct_0 @ X22)
% 0.38/0.58          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.38/0.58          | ~ (v2_struct_0 @ (k1_tex_2 @ X22 @ X23)))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.38/0.58  thf('2', plain,
% 0.38/0.58      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.58  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('4', plain,
% 0.38/0.58      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['2', '3'])).
% 0.38/0.58  thf('5', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('6', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.38/0.58      inference('clc', [status(thm)], ['4', '5'])).
% 0.38/0.58  thf('7', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('8', plain,
% 0.38/0.58      (![X22 : $i, X23 : $i]:
% 0.38/0.58         (~ (l1_pre_topc @ X22)
% 0.38/0.58          | (v2_struct_0 @ X22)
% 0.38/0.58          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.38/0.58          | (m1_pre_topc @ (k1_tex_2 @ X22 @ X23) @ X22))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.38/0.58  thf('9', plain,
% 0.38/0.58      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.58  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('11', plain,
% 0.38/0.58      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.38/0.58        | (v2_struct_0 @ sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.58  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('13', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.38/0.58      inference('clc', [status(thm)], ['11', '12'])).
% 0.38/0.58  thf(t1_tsep_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( l1_pre_topc @ A ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( m1_pre_topc @ B @ A ) =>
% 0.38/0.58           ( m1_subset_1 @
% 0.38/0.58             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.38/0.58  thf('14', plain,
% 0.38/0.58      (![X11 : $i, X12 : $i]:
% 0.38/0.58         (~ (m1_pre_topc @ X11 @ X12)
% 0.38/0.58          | (m1_subset_1 @ (u1_struct_0 @ X11) @ 
% 0.38/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.38/0.58          | ~ (l1_pre_topc @ X12))),
% 0.38/0.58      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.38/0.58  thf('15', plain,
% 0.38/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.58        | (m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.58           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.38/0.58  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('17', plain,
% 0.38/0.58      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.58      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.58  thf(cc2_tex_2, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.58           ( ( ~( v1_xboole_0 @ B ) ) => ( ~( v1_subset_1 @ B @ A ) ) ) ) ) ))).
% 0.38/0.58  thf('18', plain,
% 0.38/0.58      (![X13 : $i, X14 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.38/0.58          | ~ (v1_subset_1 @ X13 @ X14)
% 0.38/0.58          | (v1_xboole_0 @ X13)
% 0.38/0.58          | ~ (v1_zfmisc_1 @ X14)
% 0.38/0.58          | (v1_xboole_0 @ X14))),
% 0.38/0.58      inference('cnf', [status(esa)], [cc2_tex_2])).
% 0.38/0.58  thf('19', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.58        | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))
% 0.38/0.58        | ~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.58             (u1_struct_0 @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.58  thf('20', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(dt_k6_domain_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.38/0.58       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.38/0.58  thf('21', plain,
% 0.38/0.58      (![X9 : $i, X10 : $i]:
% 0.38/0.58         ((v1_xboole_0 @ X9)
% 0.38/0.58          | ~ (m1_subset_1 @ X10 @ X9)
% 0.38/0.58          | (m1_subset_1 @ (k6_domain_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9)))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.38/0.58  thf('22', plain,
% 0.38/0.58      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.58  thf(d7_subset_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.58       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.38/0.58  thf('23', plain,
% 0.38/0.58      (![X20 : $i, X21 : $i]:
% 0.38/0.58         (((X21) = (X20))
% 0.38/0.58          | (v1_subset_1 @ X21 @ X20)
% 0.38/0.58          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.38/0.58  thf('24', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.58        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.58           (u1_struct_0 @ sk_A))
% 0.38/0.58        | ((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.38/0.58  thf('25', plain,
% 0.38/0.58      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.58           (u1_struct_0 @ sk_A))
% 0.38/0.58        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('26', plain,
% 0.38/0.58      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.58           (u1_struct_0 @ sk_A)))
% 0.38/0.58         <= (~
% 0.38/0.58             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.58               (u1_struct_0 @ sk_A))))),
% 0.38/0.58      inference('split', [status(esa)], ['25'])).
% 0.38/0.58  thf('27', plain,
% 0.38/0.58      (((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.38/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.38/0.58         <= (~
% 0.38/0.58             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.58               (u1_struct_0 @ sk_A))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['24', '26'])).
% 0.38/0.58  thf(d1_tex_2, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.58       ( ( v1_zfmisc_1 @ A ) <=>
% 0.38/0.58         ( ?[B:$i]:
% 0.38/0.58           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.38/0.58  thf('28', plain,
% 0.38/0.58      (![X15 : $i, X16 : $i]:
% 0.38/0.58         (((X15) != (k6_domain_1 @ X15 @ X16))
% 0.38/0.58          | ~ (m1_subset_1 @ X16 @ X15)
% 0.38/0.58          | (v1_zfmisc_1 @ X15)
% 0.38/0.58          | (v1_xboole_0 @ X15))),
% 0.38/0.58      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.38/0.58  thf('29', plain,
% 0.38/0.58      (((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.38/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.58         | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.38/0.58         | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.38/0.58         <= (~
% 0.38/0.58             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.58               (u1_struct_0 @ sk_A))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['27', '28'])).
% 0.38/0.58  thf('30', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('31', plain,
% 0.38/0.58      (((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 0.38/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.58         | (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.38/0.58         <= (~
% 0.38/0.58             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.58               (u1_struct_0 @ sk_A))))),
% 0.38/0.58      inference('demod', [status(thm)], ['29', '30'])).
% 0.38/0.58  thf('32', plain,
% 0.38/0.58      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.38/0.58         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.38/0.58         <= (~
% 0.38/0.58             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.58               (u1_struct_0 @ sk_A))))),
% 0.38/0.58      inference('simplify', [status(thm)], ['31'])).
% 0.38/0.58  thf(cc1_zfmisc_1, axiom,
% 0.38/0.58    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_zfmisc_1 @ A ) ))).
% 0.38/0.58  thf('33', plain, (![X0 : $i]: ((v1_zfmisc_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.38/0.58      inference('cnf', [status(esa)], [cc1_zfmisc_1])).
% 0.38/0.58  thf('34', plain,
% 0.38/0.58      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.58         <= (~
% 0.38/0.58             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.58               (u1_struct_0 @ sk_A))))),
% 0.38/0.58      inference('clc', [status(thm)], ['32', '33'])).
% 0.38/0.58  thf('35', plain,
% 0.38/0.58      (~
% 0.38/0.58       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.58         (u1_struct_0 @ sk_A))) | 
% 0.38/0.58       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.38/0.58      inference('split', [status(esa)], ['25'])).
% 0.38/0.58  thf('36', plain,
% 0.38/0.58      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.58      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.58  thf('37', plain,
% 0.38/0.58      (![X20 : $i, X21 : $i]:
% 0.38/0.58         (((X21) = (X20))
% 0.38/0.58          | (v1_subset_1 @ X21 @ X20)
% 0.38/0.58          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.38/0.58  thf('38', plain,
% 0.38/0.58      (((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.58         (u1_struct_0 @ sk_A))
% 0.38/0.58        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.58  thf('39', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.38/0.58      inference('clc', [status(thm)], ['11', '12'])).
% 0.38/0.58  thf(d3_tex_2, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( l1_pre_topc @ A ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( m1_pre_topc @ B @ A ) =>
% 0.38/0.58           ( ( v1_tex_2 @ B @ A ) <=>
% 0.38/0.58             ( ![C:$i]:
% 0.38/0.58               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.58                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.38/0.58                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.38/0.58  thf('40', plain,
% 0.38/0.58      (![X17 : $i, X18 : $i]:
% 0.38/0.58         (~ (m1_pre_topc @ X17 @ X18)
% 0.38/0.58          | ((sk_C @ X17 @ X18) = (u1_struct_0 @ X17))
% 0.38/0.58          | (v1_tex_2 @ X17 @ X18)
% 0.38/0.58          | ~ (l1_pre_topc @ X18))),
% 0.38/0.58      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.38/0.58  thf('41', plain,
% 0.38/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.38/0.58        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.38/0.58        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.38/0.58            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['39', '40'])).
% 0.38/0.58  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('43', plain,
% 0.38/0.58      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.38/0.58        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.38/0.58            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.38/0.58      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.58  thf('44', plain,
% 0.38/0.58      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.38/0.58         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.58      inference('split', [status(esa)], ['25'])).
% 0.38/0.58  thf('45', plain,
% 0.38/0.58      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.38/0.58          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.38/0.58         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['43', '44'])).
% 0.38/0.58  thf('46', plain,
% 0.38/0.58      (![X17 : $i, X18 : $i]:
% 0.38/0.58         (~ (m1_pre_topc @ X17 @ X18)
% 0.38/0.58          | ~ (v1_subset_1 @ (sk_C @ X17 @ X18) @ (u1_struct_0 @ X18))
% 0.38/0.58          | (v1_tex_2 @ X17 @ X18)
% 0.38/0.58          | ~ (l1_pre_topc @ X18))),
% 0.38/0.58      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.38/0.58  thf('47', plain,
% 0.38/0.58      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.58            (u1_struct_0 @ sk_A))
% 0.38/0.58         | ~ (l1_pre_topc @ sk_A)
% 0.38/0.58         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.38/0.58         | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))
% 0.38/0.58         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['45', '46'])).
% 0.38/0.58  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('49', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.38/0.58      inference('clc', [status(thm)], ['11', '12'])).
% 0.38/0.58  thf('50', plain,
% 0.38/0.58      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.58            (u1_struct_0 @ sk_A))
% 0.38/0.58         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))
% 0.38/0.58         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.58      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.38/0.58  thf('51', plain,
% 0.38/0.58      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.38/0.58         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.58      inference('split', [status(esa)], ['25'])).
% 0.38/0.58  thf('52', plain,
% 0.38/0.58      ((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.58           (u1_struct_0 @ sk_A)))
% 0.38/0.58         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.58      inference('clc', [status(thm)], ['50', '51'])).
% 0.38/0.58  thf('53', plain,
% 0.38/0.58      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))
% 0.38/0.58         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['38', '52'])).
% 0.38/0.58  thf(fc7_struct_0, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.38/0.58       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.38/0.58  thf('54', plain,
% 0.38/0.58      (![X8 : $i]:
% 0.38/0.58         ((v1_zfmisc_1 @ (u1_struct_0 @ X8))
% 0.38/0.58          | ~ (l1_struct_0 @ X8)
% 0.38/0.58          | ~ (v7_struct_0 @ X8))),
% 0.38/0.58      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.38/0.58  thf('55', plain,
% 0.38/0.58      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.38/0.58         | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.38/0.58         | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.38/0.58         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['53', '54'])).
% 0.38/0.58  thf('56', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(fc2_tex_2, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.38/0.58         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.38/0.58       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.38/0.58         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.38/0.58         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.38/0.58  thf('57', plain,
% 0.38/0.58      (![X24 : $i, X25 : $i]:
% 0.38/0.58         (~ (l1_pre_topc @ X24)
% 0.38/0.58          | (v2_struct_0 @ X24)
% 0.38/0.58          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.38/0.58          | (v7_struct_0 @ (k1_tex_2 @ X24 @ X25)))),
% 0.38/0.58      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.38/0.58  thf('58', plain,
% 0.38/0.58      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.38/0.58        | (v2_struct_0 @ sk_A)
% 0.38/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['56', '57'])).
% 0.38/0.58  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('60', plain,
% 0.38/0.58      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.38/0.58      inference('demod', [status(thm)], ['58', '59'])).
% 0.38/0.58  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('62', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.38/0.58      inference('clc', [status(thm)], ['60', '61'])).
% 0.38/0.58  thf('63', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.38/0.58      inference('clc', [status(thm)], ['11', '12'])).
% 0.38/0.58  thf(dt_m1_pre_topc, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( l1_pre_topc @ A ) =>
% 0.38/0.58       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.38/0.58  thf('64', plain,
% 0.38/0.58      (![X4 : $i, X5 : $i]:
% 0.38/0.58         (~ (m1_pre_topc @ X4 @ X5) | (l1_pre_topc @ X4) | ~ (l1_pre_topc @ X5))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.38/0.58  thf('65', plain,
% 0.38/0.58      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['63', '64'])).
% 0.38/0.58  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('67', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['65', '66'])).
% 0.38/0.58  thf(dt_l1_pre_topc, axiom,
% 0.38/0.58    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.38/0.58  thf('68', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.58  thf('69', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['67', '68'])).
% 0.38/0.58  thf('70', plain,
% 0.38/0.58      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.38/0.58         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.58      inference('demod', [status(thm)], ['55', '62', '69'])).
% 0.38/0.58  thf(fc6_struct_0, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v7_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.38/0.58       ( ~( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.38/0.58  thf('71', plain,
% 0.38/0.58      (![X7 : $i]:
% 0.38/0.58         (~ (v1_zfmisc_1 @ (u1_struct_0 @ X7))
% 0.38/0.58          | ~ (l1_struct_0 @ X7)
% 0.38/0.58          | (v7_struct_0 @ X7))),
% 0.38/0.58      inference('cnf', [status(esa)], [fc6_struct_0])).
% 0.38/0.58  thf('72', plain,
% 0.38/0.58      ((((v7_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.38/0.58         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['70', '71'])).
% 0.38/0.58  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('74', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.38/0.58  thf('75', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.58      inference('sup-', [status(thm)], ['73', '74'])).
% 0.38/0.58  thf('76', plain,
% 0.38/0.58      (((v7_struct_0 @ sk_A))
% 0.38/0.58         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.58      inference('demod', [status(thm)], ['72', '75'])).
% 0.38/0.58  thf('77', plain,
% 0.38/0.58      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.58         (u1_struct_0 @ sk_A))
% 0.38/0.58        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('78', plain,
% 0.38/0.58      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.58         (u1_struct_0 @ sk_A)))
% 0.38/0.58         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.58               (u1_struct_0 @ sk_A))))),
% 0.38/0.58      inference('split', [status(esa)], ['77'])).
% 0.38/0.58  thf(t8_tex_2, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.38/0.58           ( ~( ( v1_subset_1 @
% 0.38/0.58                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.38/0.58                  ( u1_struct_0 @ A ) ) & 
% 0.38/0.58                ( v7_struct_0 @ A ) ) ) ) ) ))).
% 0.38/0.58  thf('79', plain,
% 0.38/0.58      (![X26 : $i, X27 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 0.38/0.58          | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X27) @ X26) @ 
% 0.38/0.58               (u1_struct_0 @ X27))
% 0.38/0.58          | ~ (v7_struct_0 @ X27)
% 0.38/0.58          | ~ (l1_struct_0 @ X27)
% 0.38/0.58          | (v2_struct_0 @ X27))),
% 0.38/0.58      inference('cnf', [status(esa)], [t8_tex_2])).
% 0.38/0.58  thf('80', plain,
% 0.38/0.58      ((((v2_struct_0 @ sk_A)
% 0.38/0.58         | ~ (l1_struct_0 @ sk_A)
% 0.38/0.58         | ~ (v7_struct_0 @ sk_A)
% 0.38/0.58         | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.38/0.58         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.58               (u1_struct_0 @ sk_A))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['78', '79'])).
% 0.38/0.58  thf('81', plain, ((l1_struct_0 @ sk_A)),
% 0.38/0.58      inference('sup-', [status(thm)], ['73', '74'])).
% 0.38/0.58  thf('82', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('83', plain,
% 0.38/0.58      ((((v2_struct_0 @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 0.38/0.58         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.58               (u1_struct_0 @ sk_A))))),
% 0.38/0.58      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.38/0.58  thf('84', plain, (~ (v2_struct_0 @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('85', plain,
% 0.38/0.58      ((~ (v7_struct_0 @ sk_A))
% 0.38/0.58         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.58               (u1_struct_0 @ sk_A))))),
% 0.38/0.58      inference('clc', [status(thm)], ['83', '84'])).
% 0.38/0.58  thf('86', plain,
% 0.38/0.58      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) | 
% 0.38/0.58       ~
% 0.38/0.58       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.58         (u1_struct_0 @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['76', '85'])).
% 0.38/0.58  thf('87', plain,
% 0.38/0.58      (~
% 0.38/0.58       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.58         (u1_struct_0 @ sk_A)))),
% 0.38/0.58      inference('sat_resolution*', [status(thm)], ['35', '86'])).
% 0.38/0.58  thf('88', plain, ((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))),
% 0.38/0.58      inference('simpl_trail', [status(thm)], ['34', '87'])).
% 0.38/0.58  thf('89', plain,
% 0.38/0.58      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.38/0.58         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.58      inference('split', [status(esa)], ['77'])).
% 0.38/0.58  thf('90', plain,
% 0.38/0.58      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.58      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.58  thf('91', plain,
% 0.38/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.58         (~ (m1_pre_topc @ X17 @ X18)
% 0.38/0.58          | ~ (v1_tex_2 @ X17 @ X18)
% 0.38/0.58          | ((X19) != (u1_struct_0 @ X17))
% 0.38/0.58          | (v1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 0.38/0.58          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.38/0.58          | ~ (l1_pre_topc @ X18))),
% 0.38/0.58      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.38/0.58  thf('92', plain,
% 0.38/0.58      (![X17 : $i, X18 : $i]:
% 0.38/0.58         (~ (l1_pre_topc @ X18)
% 0.38/0.58          | ~ (m1_subset_1 @ (u1_struct_0 @ X17) @ 
% 0.38/0.58               (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.38/0.58          | (v1_subset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X18))
% 0.38/0.58          | ~ (v1_tex_2 @ X17 @ X18)
% 0.38/0.58          | ~ (m1_pre_topc @ X17 @ X18))),
% 0.38/0.58      inference('simplify', [status(thm)], ['91'])).
% 0.38/0.58  thf('93', plain,
% 0.38/0.58      ((~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.38/0.58        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.38/0.58        | (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.58           (u1_struct_0 @ sk_A))
% 0.38/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.38/0.58      inference('sup-', [status(thm)], ['90', '92'])).
% 0.38/0.58  thf('94', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.38/0.58      inference('clc', [status(thm)], ['11', '12'])).
% 0.38/0.58  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf('96', plain,
% 0.38/0.58      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.38/0.58        | (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.58           (u1_struct_0 @ sk_A)))),
% 0.38/0.58      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.38/0.58  thf('97', plain,
% 0.38/0.58      (((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.58         (u1_struct_0 @ sk_A)))
% 0.38/0.58         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['89', '96'])).
% 0.38/0.58  thf('98', plain,
% 0.38/0.58      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) | 
% 0.38/0.58       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.38/0.58         (u1_struct_0 @ sk_A)))),
% 0.38/0.58      inference('split', [status(esa)], ['77'])).
% 0.38/0.58  thf('99', plain, (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.38/0.58      inference('sat_resolution*', [status(thm)], ['35', '86', '98'])).
% 0.38/0.58  thf('100', plain,
% 0.38/0.58      ((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.58        (u1_struct_0 @ sk_A))),
% 0.38/0.58      inference('simpl_trail', [status(thm)], ['97', '99'])).
% 0.38/0.58  thf('101', plain,
% 0.38/0.58      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.58        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.38/0.58      inference('demod', [status(thm)], ['19', '88', '100'])).
% 0.38/0.58  thf('102', plain,
% 0.38/0.58      (((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.58         (u1_struct_0 @ sk_A)))
% 0.38/0.58         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['89', '96'])).
% 0.38/0.58  thf('103', plain,
% 0.38/0.58      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.38/0.58      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.58  thf(cc4_subset_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( v1_xboole_0 @ A ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.38/0.58           ( ~( v1_subset_1 @ B @ A ) ) ) ) ))).
% 0.38/0.58  thf('104', plain,
% 0.38/0.58      (![X1 : $i, X2 : $i]:
% 0.38/0.58         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.38/0.58          | ~ (v1_subset_1 @ X1 @ X2)
% 0.38/0.58          | ~ (v1_xboole_0 @ X2))),
% 0.38/0.58      inference('cnf', [status(esa)], [cc4_subset_1])).
% 0.38/0.58  thf('105', plain,
% 0.38/0.58      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.38/0.58        | ~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.38/0.58             (u1_struct_0 @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['103', '104'])).
% 0.38/0.58  thf('106', plain,
% 0.38/0.58      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.38/0.58         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['102', '105'])).
% 0.38/0.58  thf('107', plain, (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.38/0.58      inference('sat_resolution*', [status(thm)], ['35', '86', '98'])).
% 0.38/0.58  thf('108', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.38/0.58      inference('simpl_trail', [status(thm)], ['106', '107'])).
% 0.38/0.58  thf('109', plain,
% 0.38/0.58      ((v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.38/0.58      inference('clc', [status(thm)], ['101', '108'])).
% 0.38/0.58  thf(fc2_struct_0, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.38/0.58       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.38/0.58  thf('110', plain,
% 0.38/0.58      (![X6 : $i]:
% 0.38/0.58         (~ (v1_xboole_0 @ (u1_struct_0 @ X6))
% 0.38/0.58          | ~ (l1_struct_0 @ X6)
% 0.38/0.58          | (v2_struct_0 @ X6))),
% 0.38/0.58      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.38/0.58  thf('111', plain,
% 0.38/0.58      (((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.38/0.58        | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['109', '110'])).
% 0.38/0.58  thf('112', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.38/0.58      inference('sup-', [status(thm)], ['67', '68'])).
% 0.38/0.58  thf('113', plain, ((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.38/0.58      inference('demod', [status(thm)], ['111', '112'])).
% 0.38/0.58  thf('114', plain, ($false), inference('demod', [status(thm)], ['6', '113'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.38/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
