%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZzX38b8wvs

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:07 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  256 (1418 expanded)
%              Number of leaves         :   45 ( 408 expanded)
%              Depth                    :   30
%              Number of atoms          : 2151 (17370 expanded)
%              Number of equality atoms :   59 ( 212 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X34 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X34 @ X35 ) ) ) ),
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

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( m1_subset_1 @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t7_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) )).

thf('13',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ X41 )
      | ( v1_subset_1 @ ( k6_domain_1 @ X41 @ X40 ) @ X41 )
      | ( v1_zfmisc_1 @ X41 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t7_tex_2])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_zfmisc_1 @ X0 )
      | ( v1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ X0 )
      | ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(cc1_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_zfmisc_1 @ A ) ) )).

thf('16',plain,(
    ! [X9: $i] :
      ( ( v1_zfmisc_1 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_zfmisc_1 @ X0 )
      | ( v1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(t8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) )
              & ( v7_struct_0 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X43 ) )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X43 ) @ X42 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( v7_struct_0 @ X43 )
      | ~ ( l1_struct_0 @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t8_tex_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf('21',plain,(
    ! [X9: $i] :
      ( ( v1_zfmisc_1 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v7_struct_0 @ X0 )
      | ( v1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v7_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('26',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ X25 )
      | ( ( k6_domain_1 @ X25 @ X26 )
        = ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('27',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('29',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ X23 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('30',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('33',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X33 = X32 )
      | ( v1_subset_1 @ X33 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('36',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ( ~ ( v1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( ( ( ( k1_tarski @ sk_B_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_tarski @ sk_B_1 )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('41',plain,(
    ! [X22: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('42',plain,
    ( ( ( ( k1_tarski @ sk_B_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('44',plain,(
    ! [X19: $i] :
      ( ( l1_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('45',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( ( k1_tarski @ sk_B_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X34 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X34 @ X35 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('51',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['53','54'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('56',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('57',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['48','59'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('61',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('64',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('67',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X33 = X32 )
      | ( v1_subset_1 @ X33 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('68',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['53','54'])).

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

thf('70',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ( ( sk_C_1 @ X29 @ X30 )
        = ( u1_struct_0 @ X29 ) )
      | ( v1_tex_2 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('71',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( ( sk_C_1 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( ( sk_C_1 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('75',plain,
    ( ( ( sk_C_1 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( v1_subset_1 @ ( sk_C_1 @ X29 @ X30 ) @ ( u1_struct_0 @ X30 ) )
      | ( v1_tex_2 @ X29 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('77',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['53','54'])).

thf('80',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('82',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['68','82'])).

thf('84',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X43 ) )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X43 ) @ X42 ) @ ( u1_struct_0 @ X43 ) )
      | ~ ( v7_struct_0 @ X43 )
      | ~ ( l1_struct_0 @ X43 )
      | ( v2_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t8_tex_2])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
        | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
        | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['68','82'])).

thf('87',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['53','54'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('88',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( l1_pre_topc @ X20 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
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
    ! [X19: $i] :
      ( ( l1_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('93',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
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

thf('95',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( l1_pre_topc @ X36 )
      | ( v2_struct_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X36 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('96',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['68','82'])).

thf('102',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['85','86','93','100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('104',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['65','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['63','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['62','108'])).

thf('110',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
    | ( r2_hidden @ ( sk_B @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) @ ( k1_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['24','109'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('111',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( X6 = X3 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('112',plain,(
    ! [X3: $i,X6: $i] :
      ( ( X6 = X3 )
      | ~ ( r2_hidden @ X6 @ ( k1_tarski @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
    | ( ( sk_B @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['110','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('116',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ X25 )
      | ( ( k6_domain_1 @ X25 @ X26 )
        = ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('120',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ X23 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['118','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X33 = X32 )
      | ( v1_subset_1 @ X33 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf(t6_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
              & ( v1_zfmisc_1 @ A ) ) ) ) )).

thf('128',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ X39 )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ X39 @ X38 ) @ X39 )
      | ~ ( v1_zfmisc_1 @ X39 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t6_tex_2])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ~ ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ~ ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['126','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['114','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k1_tarski @ ( sk_B @ X0 ) )
        = X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('135',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('136',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('137',plain,(
    ! [X3: $i,X6: $i] :
      ( ( X6 = X3 )
      | ~ ( r2_hidden @ X6 @ ( k1_tarski @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( X4 != X3 )
      | ( r2_hidden @ X4 @ X5 )
      | ( X5
       != ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('140',plain,(
    ! [X3: $i] :
      ( r2_hidden @ X3 @ ( k1_tarski @ X3 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('142',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(clc,[status(thm)],['138','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['135','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_subset_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
      | ( v1_xboole_0 @ ( k2_tarski @ X0 @ X0 ) )
      | ~ ( v1_zfmisc_1 @ ( k2_tarski @ X0 @ X0 ) )
      | ~ ( m1_subset_1 @ ( sk_B @ ( k2_tarski @ X0 @ X0 ) ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['135','143'])).

thf('148',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('149',plain,(
    ! [X3: $i] :
      ( r2_hidden @ X3 @ ( k1_tarski @ X3 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('150',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('152',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
      | ( v1_xboole_0 @ ( k2_tarski @ X0 @ X0 ) )
      | ~ ( v1_zfmisc_1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['146','147','152'])).

thf('154',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('155',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('156',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ ( k2_tarski @ X0 @ X0 ) )
      | ~ ( v1_subset_1 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['153','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ X0 @ ( k2_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ~ ( v1_zfmisc_1 @ ( k2_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['134','157'])).

thf('159',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('160',plain,(
    ! [X8: $i] :
      ( ( k2_tarski @ X8 @ X8 )
      = ( k1_tarski @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ X0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ~ ( v1_zfmisc_1 @ ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('162',plain,(
    ! [X3: $i] :
      ( r2_hidden @ X3 @ ( k1_tarski @ X3 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('163',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('164',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X40 @ X41 )
      | ( v1_subset_1 @ ( k6_domain_1 @ X41 @ X40 ) @ X41 )
      | ( v1_zfmisc_1 @ X41 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t7_tex_2])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( v1_zfmisc_1 @ ( k1_tarski @ X0 ) )
      | ( v1_subset_1 @ ( k6_domain_1 @ ( k1_tarski @ X0 ) @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('168',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ X25 )
      | ( ( k6_domain_1 @ X25 @ X26 )
        = ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ ( k1_tarski @ X0 ) @ X0 )
        = ( k1_tarski @ X0 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( k6_domain_1 @ ( k1_tarski @ X0 ) @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( v1_zfmisc_1 @ ( k1_tarski @ X0 ) )
      | ( v1_subset_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['166','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( v1_subset_1 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      | ( v1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['172','173'])).

thf(fc14_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) )).

thf('175',plain,(
    ! [X18: $i] :
      ~ ( v1_subset_1 @ ( k2_subset_1 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[fc14_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('176',plain,(
    ! [X13: $i] :
      ( ( k2_subset_1 @ X13 )
      = X13 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('177',plain,(
    ! [X18: $i] :
      ~ ( v1_subset_1 @ X18 @ X18 ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( v1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['174','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( v1_subset_1 @ X0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['161','178'])).

thf('180',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['113','179'])).

thf('181',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['64'])).

thf('182',plain,(
    m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('183',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( v1_tex_2 @ X29 @ X30 )
      | ( X31
       != ( u1_struct_0 @ X29 ) )
      | ( v1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('184',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X29 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X30 ) )
      | ~ ( v1_tex_2 @ X29 @ X30 )
      | ~ ( m1_pre_topc @ X29 @ X30 ) ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,
    ( ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['182','184'])).

thf('186',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['53','54'])).

thf('187',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['185','186','187'])).

thf('189',plain,
    ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['181','188'])).

thf('190',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['64'])).

thf('191',plain,(
    v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference('sat_resolution*',[status(thm)],['63','107','190'])).

thf('192',plain,(
    v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['189','191'])).

thf('193',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('194',plain,(
    ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['63','107'])).

thf('195',plain,
    ( ( k1_tarski @ sk_B_1 )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['193','194'])).

thf('196',plain,(
    v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_tarski @ sk_B_1 ) ),
    inference(demod,[status(thm)],['192','195'])).

thf('197',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['180','196'])).

thf('198',plain,
    ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,
    ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['23','198'])).

thf('200',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('201',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('202',plain,
    ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['199','200','201'])).

thf('203',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('204',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['202','203'])).

thf('205',plain,(
    ! [X22: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('206',plain,
    ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('208',plain,(
    v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,(
    $false ),
    inference(demod,[status(thm)],['6','208'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZzX38b8wvs
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:48:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 425 iterations in 0.168s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.43/0.62  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.43/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.62  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.43/0.62  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.43/0.62  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.43/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.43/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.43/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.43/0.62  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.43/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.62  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.43/0.62  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.43/0.62  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.43/0.62  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.43/0.62  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.43/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.43/0.62  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.43/0.62  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.43/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.43/0.62  thf(t20_tex_2, conjecture,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.62           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.43/0.62             ( v1_subset_1 @
% 0.43/0.62               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.62    (~( ![A:$i]:
% 0.43/0.62        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.62          ( ![B:$i]:
% 0.43/0.62            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.62              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.43/0.62                ( v1_subset_1 @
% 0.43/0.62                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.43/0.62                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.43/0.62    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.43/0.62  thf('0', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(dt_k1_tex_2, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.43/0.62         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.62       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.43/0.62         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.43/0.62         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.43/0.62  thf('1', plain,
% 0.43/0.62      (![X34 : $i, X35 : $i]:
% 0.43/0.62         (~ (l1_pre_topc @ X34)
% 0.43/0.62          | (v2_struct_0 @ X34)
% 0.43/0.62          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X34))
% 0.43/0.62          | ~ (v2_struct_0 @ (k1_tex_2 @ X34 @ X35)))),
% 0.43/0.62      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.43/0.62  thf('2', plain,
% 0.43/0.62      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.43/0.62        | (v2_struct_0 @ sk_A)
% 0.43/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.43/0.62  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('4', plain,
% 0.43/0.62      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.43/0.62      inference('demod', [status(thm)], ['2', '3'])).
% 0.43/0.62  thf('5', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('6', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.43/0.62      inference('clc', [status(thm)], ['4', '5'])).
% 0.43/0.62  thf(d1_xboole_0, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.43/0.62  thf('7', plain,
% 0.43/0.62      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.43/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.43/0.62  thf(d2_subset_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( v1_xboole_0 @ A ) =>
% 0.43/0.62         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.43/0.62       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.43/0.62         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.43/0.62  thf('8', plain,
% 0.43/0.62      (![X10 : $i, X11 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X10 @ X11)
% 0.43/0.62          | (m1_subset_1 @ X10 @ X11)
% 0.43/0.62          | (v1_xboole_0 @ X11))),
% 0.43/0.62      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.43/0.62  thf('9', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.43/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.43/0.62  thf('10', plain,
% 0.43/0.62      (![X10 : $i, X11 : $i]:
% 0.43/0.62         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.43/0.62      inference('clc', [status(thm)], ['8', '9'])).
% 0.43/0.62  thf('11', plain,
% 0.43/0.62      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['7', '10'])).
% 0.43/0.62  thf('12', plain,
% 0.43/0.62      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['7', '10'])).
% 0.43/0.62  thf(t7_tex_2, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_zfmisc_1 @ A ) ) ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( m1_subset_1 @ B @ A ) =>
% 0.43/0.62           ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) ))).
% 0.43/0.62  thf('13', plain,
% 0.43/0.62      (![X40 : $i, X41 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X40 @ X41)
% 0.43/0.62          | (v1_subset_1 @ (k6_domain_1 @ X41 @ X40) @ X41)
% 0.43/0.62          | (v1_zfmisc_1 @ X41)
% 0.43/0.62          | (v1_xboole_0 @ X41))),
% 0.43/0.62      inference('cnf', [status(esa)], [t7_tex_2])).
% 0.43/0.62  thf('14', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((v1_xboole_0 @ X0)
% 0.43/0.62          | (v1_xboole_0 @ X0)
% 0.43/0.62          | (v1_zfmisc_1 @ X0)
% 0.43/0.62          | (v1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.43/0.62  thf('15', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((v1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ X0)
% 0.43/0.62          | (v1_zfmisc_1 @ X0)
% 0.43/0.62          | (v1_xboole_0 @ X0))),
% 0.43/0.62      inference('simplify', [status(thm)], ['14'])).
% 0.43/0.62  thf(cc1_zfmisc_1, axiom,
% 0.43/0.62    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_zfmisc_1 @ A ) ))).
% 0.43/0.62  thf('16', plain, (![X9 : $i]: ((v1_zfmisc_1 @ X9) | ~ (v1_xboole_0 @ X9))),
% 0.43/0.62      inference('cnf', [status(esa)], [cc1_zfmisc_1])).
% 0.43/0.62  thf('17', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((v1_zfmisc_1 @ X0)
% 0.43/0.62          | (v1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ X0))),
% 0.43/0.62      inference('clc', [status(thm)], ['15', '16'])).
% 0.43/0.62  thf(t8_tex_2, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.43/0.62           ( ~( ( v1_subset_1 @
% 0.43/0.62                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.43/0.62                  ( u1_struct_0 @ A ) ) & 
% 0.43/0.62                ( v7_struct_0 @ A ) ) ) ) ) ))).
% 0.43/0.62  thf('18', plain,
% 0.43/0.62      (![X42 : $i, X43 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X43))
% 0.43/0.62          | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X43) @ X42) @ 
% 0.43/0.62               (u1_struct_0 @ X43))
% 0.43/0.62          | ~ (v7_struct_0 @ X43)
% 0.43/0.62          | ~ (l1_struct_0 @ X43)
% 0.43/0.62          | (v2_struct_0 @ X43))),
% 0.43/0.62      inference('cnf', [status(esa)], [t8_tex_2])).
% 0.43/0.62  thf('19', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((v1_zfmisc_1 @ (u1_struct_0 @ X0))
% 0.43/0.62          | (v2_struct_0 @ X0)
% 0.43/0.62          | ~ (l1_struct_0 @ X0)
% 0.43/0.62          | ~ (v7_struct_0 @ X0)
% 0.43/0.62          | ~ (m1_subset_1 @ (sk_B @ (u1_struct_0 @ X0)) @ (u1_struct_0 @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.43/0.62  thf('20', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.43/0.62          | ~ (v7_struct_0 @ X0)
% 0.43/0.62          | ~ (l1_struct_0 @ X0)
% 0.43/0.62          | (v2_struct_0 @ X0)
% 0.43/0.62          | (v1_zfmisc_1 @ (u1_struct_0 @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['11', '19'])).
% 0.43/0.62  thf('21', plain, (![X9 : $i]: ((v1_zfmisc_1 @ X9) | ~ (v1_xboole_0 @ X9))),
% 0.43/0.62      inference('cnf', [status(esa)], [cc1_zfmisc_1])).
% 0.43/0.62  thf('22', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((v1_zfmisc_1 @ (u1_struct_0 @ X0))
% 0.43/0.62          | (v2_struct_0 @ X0)
% 0.43/0.62          | ~ (l1_struct_0 @ X0)
% 0.43/0.62          | ~ (v7_struct_0 @ X0)
% 0.43/0.62          | (v1_zfmisc_1 @ (u1_struct_0 @ X0)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.43/0.62  thf('23', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (~ (v7_struct_0 @ X0)
% 0.43/0.62          | ~ (l1_struct_0 @ X0)
% 0.43/0.62          | (v2_struct_0 @ X0)
% 0.43/0.62          | (v1_zfmisc_1 @ (u1_struct_0 @ X0)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['22'])).
% 0.43/0.62  thf('24', plain,
% 0.43/0.62      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.43/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.43/0.62  thf('25', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(redefinition_k6_domain_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.43/0.62       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.43/0.62  thf('26', plain,
% 0.43/0.62      (![X25 : $i, X26 : $i]:
% 0.43/0.62         ((v1_xboole_0 @ X25)
% 0.43/0.62          | ~ (m1_subset_1 @ X26 @ X25)
% 0.43/0.62          | ((k6_domain_1 @ X25 @ X26) = (k1_tarski @ X26)))),
% 0.43/0.62      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.43/0.62  thf('27', plain,
% 0.43/0.62      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.43/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['25', '26'])).
% 0.43/0.62  thf('28', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(dt_k6_domain_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.43/0.62       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.43/0.62  thf('29', plain,
% 0.43/0.62      (![X23 : $i, X24 : $i]:
% 0.43/0.62         ((v1_xboole_0 @ X23)
% 0.43/0.62          | ~ (m1_subset_1 @ X24 @ X23)
% 0.43/0.62          | (m1_subset_1 @ (k6_domain_1 @ X23 @ X24) @ (k1_zfmisc_1 @ X23)))),
% 0.43/0.62      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.43/0.62  thf('30', plain,
% 0.43/0.62      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.43/0.62         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.43/0.62  thf('31', plain,
% 0.43/0.62      (((m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.43/0.62         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['27', '30'])).
% 0.43/0.62  thf('32', plain,
% 0.43/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.62        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.43/0.62           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.43/0.62      inference('simplify', [status(thm)], ['31'])).
% 0.43/0.62  thf(d7_subset_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.62       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.43/0.62  thf('33', plain,
% 0.43/0.62      (![X32 : $i, X33 : $i]:
% 0.43/0.62         (((X33) = (X32))
% 0.43/0.62          | (v1_subset_1 @ X33 @ X32)
% 0.43/0.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.43/0.62  thf('34', plain,
% 0.43/0.62      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.62        | (v1_subset_1 @ (k1_tarski @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.43/0.62        | ((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['32', '33'])).
% 0.43/0.62  thf('35', plain,
% 0.43/0.62      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.43/0.62        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['25', '26'])).
% 0.43/0.62  thf('36', plain,
% 0.43/0.62      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.43/0.62           (u1_struct_0 @ sk_A))
% 0.43/0.62        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('37', plain,
% 0.43/0.62      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.43/0.62           (u1_struct_0 @ sk_A)))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.43/0.62               (u1_struct_0 @ sk_A))))),
% 0.43/0.62      inference('split', [status(esa)], ['36'])).
% 0.43/0.62  thf('38', plain,
% 0.43/0.62      (((~ (v1_subset_1 @ (k1_tarski @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.43/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.43/0.62               (u1_struct_0 @ sk_A))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['35', '37'])).
% 0.43/0.62  thf('39', plain,
% 0.43/0.62      (((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.43/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.62         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.43/0.62               (u1_struct_0 @ sk_A))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['34', '38'])).
% 0.43/0.62  thf('40', plain,
% 0.43/0.62      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.43/0.62         | ((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A))))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.43/0.62               (u1_struct_0 @ sk_A))))),
% 0.43/0.62      inference('simplify', [status(thm)], ['39'])).
% 0.43/0.62  thf(fc2_struct_0, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.43/0.62       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.43/0.62  thf('41', plain,
% 0.43/0.62      (![X22 : $i]:
% 0.43/0.62         (~ (v1_xboole_0 @ (u1_struct_0 @ X22))
% 0.43/0.62          | ~ (l1_struct_0 @ X22)
% 0.43/0.62          | (v2_struct_0 @ X22))),
% 0.43/0.62      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.43/0.62  thf('42', plain,
% 0.43/0.62      (((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.43/0.62         | (v2_struct_0 @ sk_A)
% 0.43/0.62         | ~ (l1_struct_0 @ sk_A)))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.43/0.62               (u1_struct_0 @ sk_A))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['40', '41'])).
% 0.43/0.62  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(dt_l1_pre_topc, axiom,
% 0.43/0.62    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.43/0.62  thf('44', plain,
% 0.43/0.62      (![X19 : $i]: ((l1_struct_0 @ X19) | ~ (l1_pre_topc @ X19))),
% 0.43/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.43/0.62  thf('45', plain, ((l1_struct_0 @ sk_A)),
% 0.43/0.62      inference('sup-', [status(thm)], ['43', '44'])).
% 0.43/0.62  thf('46', plain,
% 0.43/0.62      (((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.43/0.62               (u1_struct_0 @ sk_A))))),
% 0.43/0.62      inference('demod', [status(thm)], ['42', '45'])).
% 0.43/0.62  thf('47', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('48', plain,
% 0.43/0.62      ((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.43/0.62               (u1_struct_0 @ sk_A))))),
% 0.43/0.62      inference('clc', [status(thm)], ['46', '47'])).
% 0.43/0.62  thf('49', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('50', plain,
% 0.43/0.62      (![X34 : $i, X35 : $i]:
% 0.43/0.62         (~ (l1_pre_topc @ X34)
% 0.43/0.62          | (v2_struct_0 @ X34)
% 0.43/0.62          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X34))
% 0.43/0.62          | (m1_pre_topc @ (k1_tex_2 @ X34 @ X35) @ X34))),
% 0.43/0.62      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.43/0.62  thf('51', plain,
% 0.43/0.62      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.43/0.62        | (v2_struct_0 @ sk_A)
% 0.43/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['49', '50'])).
% 0.43/0.62  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('53', plain,
% 0.43/0.62      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.43/0.62        | (v2_struct_0 @ sk_A))),
% 0.43/0.62      inference('demod', [status(thm)], ['51', '52'])).
% 0.43/0.62  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('55', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.43/0.62      inference('clc', [status(thm)], ['53', '54'])).
% 0.43/0.62  thf(t1_tsep_1, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( l1_pre_topc @ A ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( m1_pre_topc @ B @ A ) =>
% 0.43/0.62           ( m1_subset_1 @
% 0.43/0.62             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.43/0.62  thf('56', plain,
% 0.43/0.62      (![X27 : $i, X28 : $i]:
% 0.43/0.62         (~ (m1_pre_topc @ X27 @ X28)
% 0.43/0.62          | (m1_subset_1 @ (u1_struct_0 @ X27) @ 
% 0.43/0.62             (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.43/0.62          | ~ (l1_pre_topc @ X28))),
% 0.43/0.62      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.43/0.62  thf('57', plain,
% 0.43/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.43/0.62        | (m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.43/0.62           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['55', '56'])).
% 0.43/0.62  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('59', plain,
% 0.43/0.62      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.43/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('demod', [status(thm)], ['57', '58'])).
% 0.43/0.62  thf('60', plain,
% 0.43/0.62      (((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.43/0.62         (k1_zfmisc_1 @ (k1_tarski @ sk_B_1))))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.43/0.62               (u1_struct_0 @ sk_A))))),
% 0.43/0.62      inference('sup+', [status(thm)], ['48', '59'])).
% 0.43/0.62  thf(l3_subset_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.43/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.43/0.62  thf('61', plain,
% 0.43/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X15 @ X16)
% 0.43/0.62          | (r2_hidden @ X15 @ X17)
% 0.43/0.62          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.43/0.62      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.43/0.62  thf('62', plain,
% 0.43/0.62      ((![X0 : $i]:
% 0.43/0.62          ((r2_hidden @ X0 @ (k1_tarski @ sk_B_1))
% 0.43/0.62           | ~ (r2_hidden @ X0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))))
% 0.43/0.62         <= (~
% 0.43/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.43/0.62               (u1_struct_0 @ sk_A))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['60', '61'])).
% 0.43/0.62  thf('63', plain,
% 0.43/0.62      (~
% 0.43/0.62       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.43/0.62         (u1_struct_0 @ sk_A))) | 
% 0.43/0.62       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.43/0.62      inference('split', [status(esa)], ['36'])).
% 0.43/0.62  thf('64', plain,
% 0.43/0.62      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.43/0.62         (u1_struct_0 @ sk_A))
% 0.43/0.62        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('65', plain,
% 0.43/0.62      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.43/0.62         (u1_struct_0 @ sk_A)))
% 0.43/0.62         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.43/0.62               (u1_struct_0 @ sk_A))))),
% 0.43/0.62      inference('split', [status(esa)], ['64'])).
% 0.43/0.62  thf('66', plain,
% 0.43/0.62      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.43/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('demod', [status(thm)], ['57', '58'])).
% 0.43/0.62  thf('67', plain,
% 0.43/0.62      (![X32 : $i, X33 : $i]:
% 0.43/0.62         (((X33) = (X32))
% 0.43/0.62          | (v1_subset_1 @ X33 @ X32)
% 0.43/0.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.43/0.62  thf('68', plain,
% 0.43/0.62      (((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.43/0.62         (u1_struct_0 @ sk_A))
% 0.43/0.62        | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['66', '67'])).
% 0.43/0.62  thf('69', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.43/0.62      inference('clc', [status(thm)], ['53', '54'])).
% 0.43/0.62  thf(d3_tex_2, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( l1_pre_topc @ A ) =>
% 0.43/0.62       ( ![B:$i]:
% 0.43/0.62         ( ( m1_pre_topc @ B @ A ) =>
% 0.43/0.62           ( ( v1_tex_2 @ B @ A ) <=>
% 0.43/0.62             ( ![C:$i]:
% 0.43/0.62               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.62                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.43/0.62                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.43/0.62  thf('70', plain,
% 0.43/0.62      (![X29 : $i, X30 : $i]:
% 0.43/0.62         (~ (m1_pre_topc @ X29 @ X30)
% 0.43/0.62          | ((sk_C_1 @ X29 @ X30) = (u1_struct_0 @ X29))
% 0.43/0.62          | (v1_tex_2 @ X29 @ X30)
% 0.43/0.62          | ~ (l1_pre_topc @ X30))),
% 0.43/0.62      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.43/0.62  thf('71', plain,
% 0.43/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.43/0.62        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.43/0.62        | ((sk_C_1 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.43/0.62            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['69', '70'])).
% 0.43/0.62  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('73', plain,
% 0.43/0.62      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.43/0.62        | ((sk_C_1 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.43/0.62            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.43/0.62      inference('demod', [status(thm)], ['71', '72'])).
% 0.43/0.62  thf('74', plain,
% 0.43/0.62      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.43/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.43/0.62      inference('split', [status(esa)], ['36'])).
% 0.43/0.62  thf('75', plain,
% 0.43/0.62      ((((sk_C_1 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.43/0.62          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.43/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['73', '74'])).
% 0.43/0.62  thf('76', plain,
% 0.43/0.62      (![X29 : $i, X30 : $i]:
% 0.43/0.62         (~ (m1_pre_topc @ X29 @ X30)
% 0.43/0.62          | ~ (v1_subset_1 @ (sk_C_1 @ X29 @ X30) @ (u1_struct_0 @ X30))
% 0.43/0.62          | (v1_tex_2 @ X29 @ X30)
% 0.43/0.62          | ~ (l1_pre_topc @ X30))),
% 0.43/0.62      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.43/0.62  thf('77', plain,
% 0.43/0.62      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.43/0.62            (u1_struct_0 @ sk_A))
% 0.43/0.62         | ~ (l1_pre_topc @ sk_A)
% 0.43/0.62         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.43/0.62         | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))
% 0.43/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['75', '76'])).
% 0.43/0.62  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('79', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.43/0.62      inference('clc', [status(thm)], ['53', '54'])).
% 0.43/0.62  thf('80', plain,
% 0.43/0.62      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.43/0.62            (u1_struct_0 @ sk_A))
% 0.43/0.62         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))
% 0.43/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.43/0.62      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.43/0.62  thf('81', plain,
% 0.43/0.62      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.43/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.43/0.62      inference('split', [status(esa)], ['36'])).
% 0.43/0.62  thf('82', plain,
% 0.43/0.62      ((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.43/0.62           (u1_struct_0 @ sk_A)))
% 0.43/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.43/0.62      inference('clc', [status(thm)], ['80', '81'])).
% 0.43/0.62  thf('83', plain,
% 0.43/0.62      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))
% 0.43/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['68', '82'])).
% 0.43/0.62  thf('84', plain,
% 0.43/0.62      (![X42 : $i, X43 : $i]:
% 0.43/0.62         (~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X43))
% 0.43/0.62          | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X43) @ X42) @ 
% 0.43/0.62               (u1_struct_0 @ X43))
% 0.43/0.62          | ~ (v7_struct_0 @ X43)
% 0.43/0.62          | ~ (l1_struct_0 @ X43)
% 0.43/0.62          | (v2_struct_0 @ X43))),
% 0.43/0.62      inference('cnf', [status(esa)], [t8_tex_2])).
% 0.43/0.62  thf('85', plain,
% 0.43/0.62      ((![X0 : $i]:
% 0.43/0.62          (~ (v1_subset_1 @ 
% 0.43/0.62              (k6_domain_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ X0) @ 
% 0.43/0.62              (u1_struct_0 @ sk_A))
% 0.43/0.62           | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.43/0.62           | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.43/0.62           | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.43/0.62           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))))
% 0.43/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['83', '84'])).
% 0.43/0.62  thf('86', plain,
% 0.43/0.62      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))
% 0.43/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['68', '82'])).
% 0.43/0.62  thf('87', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.43/0.62      inference('clc', [status(thm)], ['53', '54'])).
% 0.43/0.62  thf(dt_m1_pre_topc, axiom,
% 0.43/0.62    (![A:$i]:
% 0.43/0.62     ( ( l1_pre_topc @ A ) =>
% 0.43/0.62       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.43/0.62  thf('88', plain,
% 0.43/0.62      (![X20 : $i, X21 : $i]:
% 0.43/0.62         (~ (m1_pre_topc @ X20 @ X21)
% 0.43/0.62          | (l1_pre_topc @ X20)
% 0.43/0.62          | ~ (l1_pre_topc @ X21))),
% 0.43/0.62      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.43/0.62  thf('89', plain,
% 0.43/0.62      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['87', '88'])).
% 0.43/0.62  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('91', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.43/0.62      inference('demod', [status(thm)], ['89', '90'])).
% 0.43/0.62  thf('92', plain,
% 0.43/0.62      (![X19 : $i]: ((l1_struct_0 @ X19) | ~ (l1_pre_topc @ X19))),
% 0.43/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.43/0.62  thf('93', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['91', '92'])).
% 0.43/0.62  thf('94', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf(fc2_tex_2, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.43/0.62         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.62       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.43/0.62         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.43/0.62         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.43/0.62  thf('95', plain,
% 0.43/0.62      (![X36 : $i, X37 : $i]:
% 0.43/0.62         (~ (l1_pre_topc @ X36)
% 0.43/0.62          | (v2_struct_0 @ X36)
% 0.43/0.62          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X36))
% 0.43/0.62          | (v7_struct_0 @ (k1_tex_2 @ X36 @ X37)))),
% 0.43/0.62      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.43/0.62  thf('96', plain,
% 0.43/0.62      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.43/0.62        | (v2_struct_0 @ sk_A)
% 0.43/0.62        | ~ (l1_pre_topc @ sk_A))),
% 0.43/0.62      inference('sup-', [status(thm)], ['94', '95'])).
% 0.43/0.62  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('98', plain,
% 0.43/0.62      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.43/0.62      inference('demod', [status(thm)], ['96', '97'])).
% 0.43/0.62  thf('99', plain, (~ (v2_struct_0 @ sk_A)),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('100', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.43/0.62      inference('clc', [status(thm)], ['98', '99'])).
% 0.43/0.62  thf('101', plain,
% 0.43/0.62      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))
% 0.43/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['68', '82'])).
% 0.43/0.62  thf('102', plain,
% 0.43/0.62      ((![X0 : $i]:
% 0.43/0.62          (~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 0.43/0.62              (u1_struct_0 @ sk_A))
% 0.43/0.62           | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.43/0.62           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))))
% 0.43/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.43/0.62      inference('demod', [status(thm)], ['85', '86', '93', '100', '101'])).
% 0.43/0.62  thf('103', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.43/0.62      inference('clc', [status(thm)], ['4', '5'])).
% 0.43/0.62  thf('104', plain,
% 0.43/0.62      ((![X0 : $i]:
% 0.43/0.62          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.43/0.62           | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 0.43/0.62                (u1_struct_0 @ sk_A))))
% 0.43/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.43/0.62      inference('clc', [status(thm)], ['102', '103'])).
% 0.43/0.62  thf('105', plain,
% 0.43/0.62      ((~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.62         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) & 
% 0.43/0.62             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.43/0.62               (u1_struct_0 @ sk_A))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['65', '104'])).
% 0.43/0.62  thf('106', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('107', plain,
% 0.43/0.62      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) | 
% 0.43/0.62       ~
% 0.43/0.62       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.43/0.62         (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('demod', [status(thm)], ['105', '106'])).
% 0.43/0.62  thf('108', plain,
% 0.43/0.62      (~
% 0.43/0.62       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.43/0.62         (u1_struct_0 @ sk_A)))),
% 0.43/0.62      inference('sat_resolution*', [status(thm)], ['63', '107'])).
% 0.43/0.62  thf('109', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((r2_hidden @ X0 @ (k1_tarski @ sk_B_1))
% 0.43/0.62          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.43/0.62      inference('simpl_trail', [status(thm)], ['62', '108'])).
% 0.43/0.62  thf('110', plain,
% 0.43/0.62      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))
% 0.43/0.62        | (r2_hidden @ (sk_B @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))) @ 
% 0.43/0.62           (k1_tarski @ sk_B_1)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['24', '109'])).
% 0.43/0.62  thf(d1_tarski, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.43/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.43/0.62  thf('111', plain,
% 0.43/0.62      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X6 @ X5) | ((X6) = (X3)) | ((X5) != (k1_tarski @ X3)))),
% 0.43/0.62      inference('cnf', [status(esa)], [d1_tarski])).
% 0.43/0.62  thf('112', plain,
% 0.43/0.62      (![X3 : $i, X6 : $i]:
% 0.43/0.62         (((X6) = (X3)) | ~ (r2_hidden @ X6 @ (k1_tarski @ X3)))),
% 0.43/0.62      inference('simplify', [status(thm)], ['111'])).
% 0.43/0.62  thf('113', plain,
% 0.43/0.62      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))
% 0.43/0.62        | ((sk_B @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))) = (sk_B_1)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['110', '112'])).
% 0.43/0.62  thf('114', plain,
% 0.43/0.62      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['7', '10'])).
% 0.43/0.62  thf('115', plain,
% 0.43/0.62      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['7', '10'])).
% 0.43/0.62  thf('116', plain,
% 0.43/0.62      (![X25 : $i, X26 : $i]:
% 0.43/0.62         ((v1_xboole_0 @ X25)
% 0.43/0.62          | ~ (m1_subset_1 @ X26 @ X25)
% 0.43/0.62          | ((k6_domain_1 @ X25 @ X26) = (k1_tarski @ X26)))),
% 0.43/0.62      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.43/0.62  thf('117', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         ((v1_xboole_0 @ X0)
% 0.43/0.62          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.43/0.62          | (v1_xboole_0 @ X0))),
% 0.43/0.62      inference('sup-', [status(thm)], ['115', '116'])).
% 0.43/0.62  thf('118', plain,
% 0.43/0.62      (![X0 : $i]:
% 0.43/0.62         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.43/0.62          | (v1_xboole_0 @ X0))),
% 0.43/0.62      inference('simplify', [status(thm)], ['117'])).
% 0.43/0.62  thf('119', plain,
% 0.43/0.62      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.43/0.63      inference('sup-', [status(thm)], ['7', '10'])).
% 0.43/0.63  thf('120', plain,
% 0.43/0.63      (![X23 : $i, X24 : $i]:
% 0.43/0.63         ((v1_xboole_0 @ X23)
% 0.43/0.63          | ~ (m1_subset_1 @ X24 @ X23)
% 0.43/0.63          | (m1_subset_1 @ (k6_domain_1 @ X23 @ X24) @ (k1_zfmisc_1 @ X23)))),
% 0.43/0.63      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.43/0.63  thf('121', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((v1_xboole_0 @ X0)
% 0.43/0.63          | (m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ 
% 0.43/0.63             (k1_zfmisc_1 @ X0))
% 0.43/0.63          | (v1_xboole_0 @ X0))),
% 0.43/0.63      inference('sup-', [status(thm)], ['119', '120'])).
% 0.43/0.63  thf('122', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((m1_subset_1 @ (k6_domain_1 @ X0 @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.43/0.63          | (v1_xboole_0 @ X0))),
% 0.43/0.63      inference('simplify', [status(thm)], ['121'])).
% 0.43/0.63  thf('123', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0))
% 0.43/0.63          | (v1_xboole_0 @ X0)
% 0.43/0.63          | (v1_xboole_0 @ X0))),
% 0.43/0.63      inference('sup+', [status(thm)], ['118', '122'])).
% 0.43/0.63  thf('124', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((v1_xboole_0 @ X0)
% 0.43/0.63          | (m1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ (k1_zfmisc_1 @ X0)))),
% 0.43/0.63      inference('simplify', [status(thm)], ['123'])).
% 0.43/0.63  thf('125', plain,
% 0.43/0.63      (![X32 : $i, X33 : $i]:
% 0.43/0.63         (((X33) = (X32))
% 0.43/0.63          | (v1_subset_1 @ X33 @ X32)
% 0.43/0.63          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 0.43/0.63      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.43/0.63  thf('126', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((v1_xboole_0 @ X0)
% 0.43/0.63          | (v1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ X0)
% 0.43/0.63          | ((k1_tarski @ (sk_B @ X0)) = (X0)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['124', '125'])).
% 0.43/0.63  thf('127', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.43/0.63          | (v1_xboole_0 @ X0))),
% 0.43/0.63      inference('simplify', [status(thm)], ['117'])).
% 0.43/0.63  thf(t6_tex_2, axiom,
% 0.43/0.63    (![A:$i]:
% 0.43/0.63     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.43/0.63       ( ![B:$i]:
% 0.43/0.63         ( ( m1_subset_1 @ B @ A ) =>
% 0.43/0.63           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.43/0.63                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.43/0.63  thf('128', plain,
% 0.43/0.63      (![X38 : $i, X39 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ X38 @ X39)
% 0.43/0.63          | ~ (v1_subset_1 @ (k6_domain_1 @ X39 @ X38) @ X39)
% 0.43/0.63          | ~ (v1_zfmisc_1 @ X39)
% 0.43/0.63          | (v1_xboole_0 @ X39))),
% 0.43/0.63      inference('cnf', [status(esa)], [t6_tex_2])).
% 0.43/0.63  thf('129', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (v1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ X0)
% 0.43/0.63          | (v1_xboole_0 @ X0)
% 0.43/0.63          | (v1_xboole_0 @ X0)
% 0.43/0.63          | ~ (v1_zfmisc_1 @ X0)
% 0.43/0.63          | ~ (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.43/0.63      inference('sup-', [status(thm)], ['127', '128'])).
% 0.43/0.63  thf('130', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ (sk_B @ X0) @ X0)
% 0.43/0.63          | ~ (v1_zfmisc_1 @ X0)
% 0.43/0.63          | (v1_xboole_0 @ X0)
% 0.43/0.63          | ~ (v1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.43/0.63      inference('simplify', [status(thm)], ['129'])).
% 0.43/0.63  thf('131', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.43/0.63          | (v1_xboole_0 @ X0)
% 0.43/0.63          | (v1_xboole_0 @ X0)
% 0.43/0.63          | ~ (v1_zfmisc_1 @ X0)
% 0.43/0.63          | ~ (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.43/0.63      inference('sup-', [status(thm)], ['126', '130'])).
% 0.43/0.63  thf('132', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ (sk_B @ X0) @ X0)
% 0.43/0.63          | ~ (v1_zfmisc_1 @ X0)
% 0.43/0.63          | (v1_xboole_0 @ X0)
% 0.43/0.63          | ((k1_tarski @ (sk_B @ X0)) = (X0)))),
% 0.43/0.63      inference('simplify', [status(thm)], ['131'])).
% 0.43/0.63  thf('133', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((v1_xboole_0 @ X0)
% 0.43/0.63          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.43/0.63          | (v1_xboole_0 @ X0)
% 0.43/0.63          | ~ (v1_zfmisc_1 @ X0))),
% 0.43/0.63      inference('sup-', [status(thm)], ['114', '132'])).
% 0.43/0.63  thf('134', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (v1_zfmisc_1 @ X0)
% 0.43/0.63          | ((k1_tarski @ (sk_B @ X0)) = (X0))
% 0.43/0.63          | (v1_xboole_0 @ X0))),
% 0.43/0.63      inference('simplify', [status(thm)], ['133'])).
% 0.43/0.63  thf(t69_enumset1, axiom,
% 0.43/0.63    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.43/0.63  thf('135', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 0.43/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.43/0.63  thf('136', plain,
% 0.43/0.63      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.43/0.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.43/0.63  thf('137', plain,
% 0.43/0.63      (![X3 : $i, X6 : $i]:
% 0.43/0.63         (((X6) = (X3)) | ~ (r2_hidden @ X6 @ (k1_tarski @ X3)))),
% 0.43/0.63      inference('simplify', [status(thm)], ['111'])).
% 0.43/0.63  thf('138', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((v1_xboole_0 @ (k1_tarski @ X0)) | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['136', '137'])).
% 0.43/0.63  thf('139', plain,
% 0.43/0.63      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.43/0.63         (((X4) != (X3)) | (r2_hidden @ X4 @ X5) | ((X5) != (k1_tarski @ X3)))),
% 0.43/0.63      inference('cnf', [status(esa)], [d1_tarski])).
% 0.43/0.63  thf('140', plain, (![X3 : $i]: (r2_hidden @ X3 @ (k1_tarski @ X3))),
% 0.43/0.63      inference('simplify', [status(thm)], ['139'])).
% 0.43/0.63  thf('141', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.43/0.63      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.43/0.63  thf('142', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.43/0.63      inference('sup-', [status(thm)], ['140', '141'])).
% 0.43/0.63  thf('143', plain, (![X0 : $i]: ((sk_B @ (k1_tarski @ X0)) = (X0))),
% 0.43/0.63      inference('clc', [status(thm)], ['138', '142'])).
% 0.43/0.63  thf('144', plain, (![X0 : $i]: ((sk_B @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.43/0.63      inference('sup+', [status(thm)], ['135', '143'])).
% 0.43/0.63  thf('145', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ (sk_B @ X0) @ X0)
% 0.43/0.63          | ~ (v1_zfmisc_1 @ X0)
% 0.43/0.63          | (v1_xboole_0 @ X0)
% 0.43/0.63          | ~ (v1_subset_1 @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.43/0.63      inference('simplify', [status(thm)], ['129'])).
% 0.43/0.63  thf('146', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (v1_subset_1 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))
% 0.43/0.63          | (v1_xboole_0 @ (k2_tarski @ X0 @ X0))
% 0.43/0.63          | ~ (v1_zfmisc_1 @ (k2_tarski @ X0 @ X0))
% 0.43/0.63          | ~ (m1_subset_1 @ (sk_B @ (k2_tarski @ X0 @ X0)) @ 
% 0.43/0.63               (k2_tarski @ X0 @ X0)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['144', '145'])).
% 0.43/0.63  thf('147', plain, (![X0 : $i]: ((sk_B @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.43/0.63      inference('sup+', [status(thm)], ['135', '143'])).
% 0.43/0.63  thf('148', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 0.43/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.43/0.63  thf('149', plain, (![X3 : $i]: (r2_hidden @ X3 @ (k1_tarski @ X3))),
% 0.43/0.63      inference('simplify', [status(thm)], ['139'])).
% 0.43/0.63  thf('150', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X0))),
% 0.43/0.63      inference('sup+', [status(thm)], ['148', '149'])).
% 0.43/0.63  thf('151', plain,
% 0.43/0.63      (![X10 : $i, X11 : $i]:
% 0.43/0.63         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.43/0.63      inference('clc', [status(thm)], ['8', '9'])).
% 0.43/0.63  thf('152', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k2_tarski @ X0 @ X0))),
% 0.43/0.63      inference('sup-', [status(thm)], ['150', '151'])).
% 0.43/0.63  thf('153', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (v1_subset_1 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))
% 0.43/0.63          | (v1_xboole_0 @ (k2_tarski @ X0 @ X0))
% 0.43/0.63          | ~ (v1_zfmisc_1 @ (k2_tarski @ X0 @ X0)))),
% 0.43/0.63      inference('demod', [status(thm)], ['146', '147', '152'])).
% 0.43/0.63  thf('154', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 0.43/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.43/0.63  thf('155', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.43/0.63      inference('sup-', [status(thm)], ['140', '141'])).
% 0.43/0.63  thf('156', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k2_tarski @ X0 @ X0))),
% 0.43/0.63      inference('sup-', [status(thm)], ['154', '155'])).
% 0.43/0.63  thf('157', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (v1_zfmisc_1 @ (k2_tarski @ X0 @ X0))
% 0.43/0.63          | ~ (v1_subset_1 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0)))),
% 0.43/0.63      inference('clc', [status(thm)], ['153', '156'])).
% 0.43/0.63  thf('158', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (v1_subset_1 @ X0 @ (k2_tarski @ (sk_B @ X0) @ (sk_B @ X0)))
% 0.43/0.63          | (v1_xboole_0 @ X0)
% 0.43/0.63          | ~ (v1_zfmisc_1 @ X0)
% 0.43/0.63          | ~ (v1_zfmisc_1 @ (k2_tarski @ (sk_B @ X0) @ (sk_B @ X0))))),
% 0.43/0.63      inference('sup-', [status(thm)], ['134', '157'])).
% 0.43/0.63  thf('159', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 0.43/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.43/0.63  thf('160', plain, (![X8 : $i]: ((k2_tarski @ X8 @ X8) = (k1_tarski @ X8))),
% 0.43/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.43/0.63  thf('161', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (v1_subset_1 @ X0 @ (k1_tarski @ (sk_B @ X0)))
% 0.43/0.63          | (v1_xboole_0 @ X0)
% 0.43/0.63          | ~ (v1_zfmisc_1 @ X0)
% 0.43/0.63          | ~ (v1_zfmisc_1 @ (k1_tarski @ (sk_B @ X0))))),
% 0.43/0.63      inference('demod', [status(thm)], ['158', '159', '160'])).
% 0.43/0.63  thf('162', plain, (![X3 : $i]: (r2_hidden @ X3 @ (k1_tarski @ X3))),
% 0.43/0.63      inference('simplify', [status(thm)], ['139'])).
% 0.43/0.63  thf('163', plain,
% 0.43/0.63      (![X10 : $i, X11 : $i]:
% 0.43/0.63         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.43/0.63      inference('clc', [status(thm)], ['8', '9'])).
% 0.43/0.63  thf('164', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_tarski @ X0))),
% 0.43/0.63      inference('sup-', [status(thm)], ['162', '163'])).
% 0.43/0.63  thf('165', plain,
% 0.43/0.63      (![X40 : $i, X41 : $i]:
% 0.43/0.63         (~ (m1_subset_1 @ X40 @ X41)
% 0.43/0.63          | (v1_subset_1 @ (k6_domain_1 @ X41 @ X40) @ X41)
% 0.43/0.63          | (v1_zfmisc_1 @ X41)
% 0.43/0.63          | (v1_xboole_0 @ X41))),
% 0.43/0.63      inference('cnf', [status(esa)], [t7_tex_2])).
% 0.43/0.63  thf('166', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((v1_xboole_0 @ (k1_tarski @ X0))
% 0.43/0.63          | (v1_zfmisc_1 @ (k1_tarski @ X0))
% 0.43/0.63          | (v1_subset_1 @ (k6_domain_1 @ (k1_tarski @ X0) @ X0) @ 
% 0.43/0.63             (k1_tarski @ X0)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['164', '165'])).
% 0.43/0.63  thf('167', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_tarski @ X0))),
% 0.43/0.63      inference('sup-', [status(thm)], ['162', '163'])).
% 0.43/0.63  thf('168', plain,
% 0.43/0.63      (![X25 : $i, X26 : $i]:
% 0.43/0.63         ((v1_xboole_0 @ X25)
% 0.43/0.63          | ~ (m1_subset_1 @ X26 @ X25)
% 0.43/0.63          | ((k6_domain_1 @ X25 @ X26) = (k1_tarski @ X26)))),
% 0.43/0.63      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.43/0.63  thf('169', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (((k6_domain_1 @ (k1_tarski @ X0) @ X0) = (k1_tarski @ X0))
% 0.43/0.63          | (v1_xboole_0 @ (k1_tarski @ X0)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['167', '168'])).
% 0.43/0.63  thf('170', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.43/0.63      inference('sup-', [status(thm)], ['140', '141'])).
% 0.43/0.63  thf('171', plain,
% 0.43/0.63      (![X0 : $i]: ((k6_domain_1 @ (k1_tarski @ X0) @ X0) = (k1_tarski @ X0))),
% 0.43/0.63      inference('clc', [status(thm)], ['169', '170'])).
% 0.43/0.63  thf('172', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((v1_xboole_0 @ (k1_tarski @ X0))
% 0.43/0.63          | (v1_zfmisc_1 @ (k1_tarski @ X0))
% 0.43/0.63          | (v1_subset_1 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.43/0.63      inference('demod', [status(thm)], ['166', '171'])).
% 0.43/0.63  thf('173', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X0))),
% 0.43/0.63      inference('sup-', [status(thm)], ['140', '141'])).
% 0.43/0.63  thf('174', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         ((v1_subset_1 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 0.43/0.63          | (v1_zfmisc_1 @ (k1_tarski @ X0)))),
% 0.43/0.63      inference('clc', [status(thm)], ['172', '173'])).
% 0.43/0.63  thf(fc14_subset_1, axiom,
% 0.43/0.63    (![A:$i]: ( ~( v1_subset_1 @ ( k2_subset_1 @ A ) @ A ) ))).
% 0.43/0.63  thf('175', plain, (![X18 : $i]: ~ (v1_subset_1 @ (k2_subset_1 @ X18) @ X18)),
% 0.43/0.63      inference('cnf', [status(esa)], [fc14_subset_1])).
% 0.43/0.63  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.43/0.63  thf('176', plain, (![X13 : $i]: ((k2_subset_1 @ X13) = (X13))),
% 0.43/0.63      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.43/0.63  thf('177', plain, (![X18 : $i]: ~ (v1_subset_1 @ X18 @ X18)),
% 0.43/0.63      inference('demod', [status(thm)], ['175', '176'])).
% 0.43/0.63  thf('178', plain, (![X0 : $i]: (v1_zfmisc_1 @ (k1_tarski @ X0))),
% 0.43/0.63      inference('clc', [status(thm)], ['174', '177'])).
% 0.43/0.63  thf('179', plain,
% 0.43/0.63      (![X0 : $i]:
% 0.43/0.63         (~ (v1_subset_1 @ X0 @ (k1_tarski @ (sk_B @ X0)))
% 0.43/0.63          | (v1_xboole_0 @ X0)
% 0.43/0.63          | ~ (v1_zfmisc_1 @ X0))),
% 0.43/0.63      inference('demod', [status(thm)], ['161', '178'])).
% 0.43/0.63  thf('180', plain,
% 0.43/0.63      ((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.43/0.63           (k1_tarski @ sk_B_1))
% 0.43/0.63        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))
% 0.43/0.63        | ~ (v1_zfmisc_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))
% 0.43/0.63        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.43/0.63      inference('sup-', [status(thm)], ['113', '179'])).
% 0.43/0.63  thf('181', plain,
% 0.43/0.63      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.43/0.63         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.43/0.63      inference('split', [status(esa)], ['64'])).
% 0.43/0.63  thf('182', plain,
% 0.43/0.63      ((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.43/0.63        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.63      inference('demod', [status(thm)], ['57', '58'])).
% 0.43/0.63  thf('183', plain,
% 0.43/0.63      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.43/0.63         (~ (m1_pre_topc @ X29 @ X30)
% 0.43/0.63          | ~ (v1_tex_2 @ X29 @ X30)
% 0.43/0.63          | ((X31) != (u1_struct_0 @ X29))
% 0.43/0.63          | (v1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 0.43/0.63          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.43/0.63          | ~ (l1_pre_topc @ X30))),
% 0.43/0.63      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.43/0.63  thf('184', plain,
% 0.43/0.63      (![X29 : $i, X30 : $i]:
% 0.43/0.63         (~ (l1_pre_topc @ X30)
% 0.43/0.63          | ~ (m1_subset_1 @ (u1_struct_0 @ X29) @ 
% 0.43/0.63               (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.43/0.63          | (v1_subset_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X30))
% 0.43/0.63          | ~ (v1_tex_2 @ X29 @ X30)
% 0.43/0.63          | ~ (m1_pre_topc @ X29 @ X30))),
% 0.43/0.63      inference('simplify', [status(thm)], ['183'])).
% 0.43/0.63  thf('185', plain,
% 0.43/0.63      ((~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.43/0.63        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.43/0.63        | (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.43/0.63           (u1_struct_0 @ sk_A))
% 0.43/0.63        | ~ (l1_pre_topc @ sk_A))),
% 0.43/0.63      inference('sup-', [status(thm)], ['182', '184'])).
% 0.43/0.63  thf('186', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.43/0.63      inference('clc', [status(thm)], ['53', '54'])).
% 0.43/0.63  thf('187', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.63  thf('188', plain,
% 0.43/0.63      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.43/0.63        | (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.43/0.63           (u1_struct_0 @ sk_A)))),
% 0.43/0.63      inference('demod', [status(thm)], ['185', '186', '187'])).
% 0.43/0.63  thf('189', plain,
% 0.43/0.63      (((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.43/0.63         (u1_struct_0 @ sk_A)))
% 0.43/0.63         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['181', '188'])).
% 0.43/0.63  thf('190', plain,
% 0.43/0.63      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) | 
% 0.43/0.63       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.43/0.63         (u1_struct_0 @ sk_A)))),
% 0.43/0.63      inference('split', [status(esa)], ['64'])).
% 0.43/0.63  thf('191', plain, (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.43/0.63      inference('sat_resolution*', [status(thm)], ['63', '107', '190'])).
% 0.43/0.63  thf('192', plain,
% 0.43/0.63      ((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.43/0.63        (u1_struct_0 @ sk_A))),
% 0.43/0.63      inference('simpl_trail', [status(thm)], ['189', '191'])).
% 0.43/0.63  thf('193', plain,
% 0.43/0.63      ((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.43/0.63         <= (~
% 0.43/0.63             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.43/0.63               (u1_struct_0 @ sk_A))))),
% 0.43/0.63      inference('clc', [status(thm)], ['46', '47'])).
% 0.43/0.63  thf('194', plain,
% 0.43/0.63      (~
% 0.43/0.63       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.43/0.63         (u1_struct_0 @ sk_A)))),
% 0.43/0.63      inference('sat_resolution*', [status(thm)], ['63', '107'])).
% 0.43/0.63  thf('195', plain, (((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A))),
% 0.43/0.63      inference('simpl_trail', [status(thm)], ['193', '194'])).
% 0.43/0.63  thf('196', plain,
% 0.43/0.63      ((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.43/0.63        (k1_tarski @ sk_B_1))),
% 0.43/0.63      inference('demod', [status(thm)], ['192', '195'])).
% 0.43/0.63  thf('197', plain,
% 0.43/0.63      (((v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))
% 0.43/0.63        | ~ (v1_zfmisc_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))
% 0.43/0.63        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.43/0.63      inference('demod', [status(thm)], ['180', '196'])).
% 0.43/0.63  thf('198', plain,
% 0.43/0.63      ((~ (v1_zfmisc_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))
% 0.43/0.63        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.43/0.63      inference('simplify', [status(thm)], ['197'])).
% 0.43/0.63  thf('199', plain,
% 0.43/0.63      (((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.43/0.63        | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.43/0.63        | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.43/0.63        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.43/0.63      inference('sup-', [status(thm)], ['23', '198'])).
% 0.43/0.63  thf('200', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.43/0.63      inference('sup-', [status(thm)], ['91', '92'])).
% 0.43/0.63  thf('201', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.43/0.63      inference('clc', [status(thm)], ['98', '99'])).
% 0.43/0.63  thf('202', plain,
% 0.43/0.63      (((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.43/0.63        | (v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.43/0.63      inference('demod', [status(thm)], ['199', '200', '201'])).
% 0.43/0.63  thf('203', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.43/0.63      inference('clc', [status(thm)], ['4', '5'])).
% 0.43/0.63  thf('204', plain,
% 0.43/0.63      ((v1_xboole_0 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.43/0.63      inference('clc', [status(thm)], ['202', '203'])).
% 0.43/0.63  thf('205', plain,
% 0.43/0.63      (![X22 : $i]:
% 0.43/0.63         (~ (v1_xboole_0 @ (u1_struct_0 @ X22))
% 0.43/0.63          | ~ (l1_struct_0 @ X22)
% 0.43/0.63          | (v2_struct_0 @ X22))),
% 0.43/0.63      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.43/0.63  thf('206', plain,
% 0.43/0.63      (((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.43/0.63        | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['204', '205'])).
% 0.43/0.63  thf('207', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.43/0.63      inference('sup-', [status(thm)], ['91', '92'])).
% 0.43/0.63  thf('208', plain, ((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.43/0.63      inference('demod', [status(thm)], ['206', '207'])).
% 0.43/0.63  thf('209', plain, ($false), inference('demod', [status(thm)], ['6', '208'])).
% 0.43/0.63  
% 0.43/0.63  % SZS output end Refutation
% 0.43/0.63  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
