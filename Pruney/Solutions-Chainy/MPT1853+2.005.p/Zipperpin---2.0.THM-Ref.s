%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nf8RsVEFnm

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:02 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 206 expanded)
%              Number of leaves         :   33 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          :  882 (2364 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X7 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X21 = X20 )
      | ( v1_subset_1 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( ( k6_domain_1 @ X14 @ X15 )
        = ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('11',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,
    ( ( ~ ( v1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( ( k1_tarski @ sk_B_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_tarski @ sk_B_1 )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('16',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('17',plain,
    ( ( ( ( k1_tarski @ sk_B_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('19',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('20',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( ( k1_tarski @ sk_B_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf(fc6_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('24',plain,(
    ! [X13: $i] :
      ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v7_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_struct_0])).

thf('25',plain,
    ( ( ~ ( v1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) )
      | ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(fc2_zfmisc_1,axiom,(
    ! [A: $i] :
      ( v1_zfmisc_1 @ ( k1_tarski @ A ) ) )).

thf('26',plain,(
    ! [X6: $i] :
      ( v1_zfmisc_1 @ ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc2_zfmisc_1])).

thf('27',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('28',plain,
    ( ( v7_struct_0 @ sk_A )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,(
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

thf('32',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X22 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('33',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['35','36'])).

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

thf('38',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ~ ( v1_tex_2 @ X16 @ X17 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v7_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc10_tex_2])).

thf('39',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ~ ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('45',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['42','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','52'])).

thf('54',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['29'])).

thf('55',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['35','36'])).

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

thf('56',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( v7_struct_0 @ X18 )
      | ( v1_tex_2 @ X18 @ X19 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v7_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc13_tex_2])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v7_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
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

thf('60',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('61',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v7_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','65'])).

thf('67',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('68',plain,
    ( ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('70',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v7_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v7_struct_0 @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['29'])).

thf(t8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) )
              & ( v7_struct_0 @ A ) ) ) ) )).

thf('74',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X27 ) @ X26 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( v7_struct_0 @ X27 )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t8_tex_2])).

thf('75',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('77',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['72','80'])).

thf('82',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','53','54','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nf8RsVEFnm
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:14:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.56  % Solved by: fo/fo7.sh
% 0.39/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.56  % done 123 iterations in 0.090s
% 0.39/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.56  % SZS output start Refutation
% 0.39/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.39/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.56  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.39/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.39/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.56  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.39/0.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.39/0.56  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.39/0.56  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.39/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.56  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.39/0.56  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.39/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.56  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
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
% 0.39/0.56  thf('0', plain,
% 0.39/0.56      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56           (u1_struct_0 @ sk_A))
% 0.39/0.56        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('1', plain,
% 0.39/0.56      (~
% 0.39/0.56       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56         (u1_struct_0 @ sk_A))) | 
% 0.39/0.56       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.39/0.56      inference('split', [status(esa)], ['0'])).
% 0.39/0.56  thf('2', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(t2_subset, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ A @ B ) =>
% 0.39/0.56       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.39/0.56  thf('3', plain,
% 0.39/0.56      (![X9 : $i, X10 : $i]:
% 0.39/0.56         ((r2_hidden @ X9 @ X10)
% 0.39/0.56          | (v1_xboole_0 @ X10)
% 0.39/0.56          | ~ (m1_subset_1 @ X9 @ X10))),
% 0.39/0.56      inference('cnf', [status(esa)], [t2_subset])).
% 0.39/0.56  thf('4', plain,
% 0.39/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56        | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.56  thf(t63_subset_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( r2_hidden @ A @ B ) =>
% 0.39/0.56       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.39/0.56  thf('5', plain,
% 0.39/0.56      (![X7 : $i, X8 : $i]:
% 0.39/0.56         ((m1_subset_1 @ (k1_tarski @ X7) @ (k1_zfmisc_1 @ X8))
% 0.39/0.56          | ~ (r2_hidden @ X7 @ X8))),
% 0.39/0.56      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.39/0.56  thf('6', plain,
% 0.39/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.39/0.56           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.56  thf(d7_subset_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.56       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.39/0.56  thf('7', plain,
% 0.39/0.56      (![X20 : $i, X21 : $i]:
% 0.39/0.56         (((X21) = (X20))
% 0.39/0.56          | (v1_subset_1 @ X21 @ X20)
% 0.39/0.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.39/0.56      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.39/0.56  thf('8', plain,
% 0.39/0.56      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56        | (v1_subset_1 @ (k1_tarski @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.39/0.56        | ((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.56  thf('9', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(redefinition_k6_domain_1, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.39/0.56       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.39/0.56  thf('10', plain,
% 0.39/0.56      (![X14 : $i, X15 : $i]:
% 0.39/0.56         ((v1_xboole_0 @ X14)
% 0.39/0.56          | ~ (m1_subset_1 @ X15 @ X14)
% 0.39/0.56          | ((k6_domain_1 @ X14 @ X15) = (k1_tarski @ X15)))),
% 0.39/0.56      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.39/0.56  thf('11', plain,
% 0.39/0.56      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.39/0.56        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.39/0.56  thf('12', plain,
% 0.39/0.56      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56           (u1_struct_0 @ sk_A)))
% 0.39/0.56         <= (~
% 0.39/0.56             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56               (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('split', [status(esa)], ['0'])).
% 0.39/0.56  thf('13', plain,
% 0.39/0.56      (((~ (v1_subset_1 @ (k1_tarski @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.39/0.56         <= (~
% 0.39/0.56             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56               (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.39/0.56  thf('14', plain,
% 0.39/0.56      (((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.39/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.39/0.56         <= (~
% 0.39/0.56             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56               (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['8', '13'])).
% 0.39/0.56  thf('15', plain,
% 0.39/0.56      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.39/0.56         | ((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A))))
% 0.39/0.56         <= (~
% 0.39/0.56             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56               (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('simplify', [status(thm)], ['14'])).
% 0.39/0.56  thf(fc2_struct_0, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.39/0.56       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.39/0.56  thf('16', plain,
% 0.39/0.56      (![X12 : $i]:
% 0.39/0.56         (~ (v1_xboole_0 @ (u1_struct_0 @ X12))
% 0.39/0.56          | ~ (l1_struct_0 @ X12)
% 0.39/0.56          | (v2_struct_0 @ X12))),
% 0.39/0.56      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.39/0.56  thf('17', plain,
% 0.39/0.56      (((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.39/0.56         | (v2_struct_0 @ sk_A)
% 0.39/0.56         | ~ (l1_struct_0 @ sk_A)))
% 0.39/0.56         <= (~
% 0.39/0.56             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56               (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.39/0.56  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(dt_l1_pre_topc, axiom,
% 0.39/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.39/0.56  thf('19', plain,
% 0.39/0.56      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.39/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.39/0.56  thf('20', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.56  thf('21', plain,
% 0.39/0.56      (((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.39/0.56         <= (~
% 0.39/0.56             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56               (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('demod', [status(thm)], ['17', '20'])).
% 0.39/0.56  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('23', plain,
% 0.39/0.56      ((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.39/0.56         <= (~
% 0.39/0.56             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56               (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('clc', [status(thm)], ['21', '22'])).
% 0.39/0.56  thf(fc6_struct_0, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ( ~( v7_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.39/0.56       ( ~( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.39/0.56  thf('24', plain,
% 0.39/0.56      (![X13 : $i]:
% 0.39/0.56         (~ (v1_zfmisc_1 @ (u1_struct_0 @ X13))
% 0.39/0.56          | ~ (l1_struct_0 @ X13)
% 0.39/0.56          | (v7_struct_0 @ X13))),
% 0.39/0.56      inference('cnf', [status(esa)], [fc6_struct_0])).
% 0.39/0.56  thf('25', plain,
% 0.39/0.56      (((~ (v1_zfmisc_1 @ (k1_tarski @ sk_B_1))
% 0.39/0.56         | (v7_struct_0 @ sk_A)
% 0.39/0.56         | ~ (l1_struct_0 @ sk_A)))
% 0.39/0.56         <= (~
% 0.39/0.56             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56               (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.39/0.56  thf(fc2_zfmisc_1, axiom, (![A:$i]: ( v1_zfmisc_1 @ ( k1_tarski @ A ) ))).
% 0.39/0.56  thf('26', plain, (![X6 : $i]: (v1_zfmisc_1 @ (k1_tarski @ X6))),
% 0.39/0.56      inference('cnf', [status(esa)], [fc2_zfmisc_1])).
% 0.39/0.56  thf('27', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.56  thf('28', plain,
% 0.39/0.56      (((v7_struct_0 @ sk_A))
% 0.39/0.56         <= (~
% 0.39/0.56             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56               (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.39/0.56  thf('29', plain,
% 0.39/0.56      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56         (u1_struct_0 @ sk_A))
% 0.39/0.56        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('30', plain,
% 0.39/0.56      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.39/0.56         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.39/0.56      inference('split', [status(esa)], ['29'])).
% 0.39/0.56  thf('31', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(dt_k1_tex_2, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.39/0.56         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.56       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.39/0.56         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.39/0.56         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.39/0.56  thf('32', plain,
% 0.39/0.56      (![X22 : $i, X23 : $i]:
% 0.39/0.56         (~ (l1_pre_topc @ X22)
% 0.39/0.56          | (v2_struct_0 @ X22)
% 0.39/0.56          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.39/0.56          | (m1_pre_topc @ (k1_tex_2 @ X22 @ X23) @ X22))),
% 0.39/0.56      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.39/0.56  thf('33', plain,
% 0.39/0.56      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.39/0.56        | (v2_struct_0 @ sk_A)
% 0.39/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.56  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('35', plain,
% 0.39/0.56      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.39/0.56        | (v2_struct_0 @ sk_A))),
% 0.39/0.56      inference('demod', [status(thm)], ['33', '34'])).
% 0.39/0.56  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('37', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.39/0.56      inference('clc', [status(thm)], ['35', '36'])).
% 0.39/0.56  thf(cc10_tex_2, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.39/0.56           ( ( ~( v2_struct_0 @ B ) ) =>
% 0.39/0.56             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tex_2 @ B @ A ) ) ) ) ) ) ))).
% 0.39/0.56  thf('38', plain,
% 0.39/0.56      (![X16 : $i, X17 : $i]:
% 0.39/0.56         (~ (m1_pre_topc @ X16 @ X17)
% 0.39/0.56          | ~ (v1_tex_2 @ X16 @ X17)
% 0.39/0.56          | (v2_struct_0 @ X16)
% 0.39/0.56          | ~ (l1_pre_topc @ X17)
% 0.39/0.56          | ~ (v7_struct_0 @ X17)
% 0.39/0.56          | (v2_struct_0 @ X17))),
% 0.39/0.56      inference('cnf', [status(esa)], [cc10_tex_2])).
% 0.39/0.56  thf('39', plain,
% 0.39/0.56      (((v2_struct_0 @ sk_A)
% 0.39/0.56        | ~ (v7_struct_0 @ sk_A)
% 0.39/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.56        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.39/0.56        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['37', '38'])).
% 0.39/0.56  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('41', plain,
% 0.39/0.56      (((v2_struct_0 @ sk_A)
% 0.39/0.56        | ~ (v7_struct_0 @ sk_A)
% 0.39/0.56        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.39/0.56        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.39/0.56      inference('demod', [status(thm)], ['39', '40'])).
% 0.39/0.56  thf('42', plain,
% 0.39/0.56      ((((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.39/0.56         | ~ (v7_struct_0 @ sk_A)
% 0.39/0.56         | (v2_struct_0 @ sk_A)))
% 0.39/0.56         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['30', '41'])).
% 0.39/0.56  thf('43', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('44', plain,
% 0.39/0.56      (![X22 : $i, X23 : $i]:
% 0.39/0.56         (~ (l1_pre_topc @ X22)
% 0.39/0.56          | (v2_struct_0 @ X22)
% 0.39/0.56          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.39/0.56          | ~ (v2_struct_0 @ (k1_tex_2 @ X22 @ X23)))),
% 0.39/0.56      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.39/0.56  thf('45', plain,
% 0.39/0.56      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.39/0.56        | (v2_struct_0 @ sk_A)
% 0.39/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.56  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('47', plain,
% 0.39/0.56      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.39/0.56      inference('demod', [status(thm)], ['45', '46'])).
% 0.39/0.56  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('49', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.39/0.56      inference('clc', [status(thm)], ['47', '48'])).
% 0.39/0.56  thf('50', plain,
% 0.39/0.56      ((((v2_struct_0 @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 0.39/0.56         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.39/0.56      inference('clc', [status(thm)], ['42', '49'])).
% 0.39/0.56  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('52', plain,
% 0.39/0.56      ((~ (v7_struct_0 @ sk_A))
% 0.39/0.56         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.39/0.56      inference('clc', [status(thm)], ['50', '51'])).
% 0.39/0.56  thf('53', plain,
% 0.39/0.56      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56         (u1_struct_0 @ sk_A))) | 
% 0.39/0.56       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['28', '52'])).
% 0.39/0.56  thf('54', plain,
% 0.39/0.56      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56         (u1_struct_0 @ sk_A))) | 
% 0.39/0.56       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.39/0.56      inference('split', [status(esa)], ['29'])).
% 0.39/0.56  thf('55', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.39/0.56      inference('clc', [status(thm)], ['35', '36'])).
% 0.39/0.56  thf(cc13_tex_2, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( ~( v7_struct_0 @ A ) ) & 
% 0.39/0.56         ( l1_pre_topc @ A ) ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.39/0.56           ( ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tex_2 @ B @ A ) ) ) =>
% 0.39/0.56             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v7_struct_0 @ B ) ) ) ) ) ) ))).
% 0.39/0.56  thf('56', plain,
% 0.39/0.56      (![X18 : $i, X19 : $i]:
% 0.39/0.56         (~ (m1_pre_topc @ X18 @ X19)
% 0.39/0.56          | ~ (v7_struct_0 @ X18)
% 0.39/0.56          | (v1_tex_2 @ X18 @ X19)
% 0.39/0.56          | (v2_struct_0 @ X18)
% 0.39/0.56          | ~ (l1_pre_topc @ X19)
% 0.39/0.56          | (v7_struct_0 @ X19)
% 0.39/0.56          | (v2_struct_0 @ X19))),
% 0.39/0.56      inference('cnf', [status(esa)], [cc13_tex_2])).
% 0.39/0.56  thf('57', plain,
% 0.39/0.56      (((v2_struct_0 @ sk_A)
% 0.39/0.56        | (v7_struct_0 @ sk_A)
% 0.39/0.56        | ~ (l1_pre_topc @ sk_A)
% 0.39/0.56        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.39/0.56        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.39/0.56        | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['55', '56'])).
% 0.39/0.56  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('59', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(fc2_tex_2, axiom,
% 0.39/0.56    (![A:$i,B:$i]:
% 0.39/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.39/0.56         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.56       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.39/0.56         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.39/0.56         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.39/0.56  thf('60', plain,
% 0.39/0.56      (![X24 : $i, X25 : $i]:
% 0.39/0.56         (~ (l1_pre_topc @ X24)
% 0.39/0.56          | (v2_struct_0 @ X24)
% 0.39/0.56          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.39/0.56          | (v7_struct_0 @ (k1_tex_2 @ X24 @ X25)))),
% 0.39/0.56      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.39/0.56  thf('61', plain,
% 0.39/0.56      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.39/0.56        | (v2_struct_0 @ sk_A)
% 0.39/0.56        | ~ (l1_pre_topc @ sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['59', '60'])).
% 0.39/0.56  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('63', plain,
% 0.39/0.56      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.39/0.56      inference('demod', [status(thm)], ['61', '62'])).
% 0.39/0.56  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('65', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.39/0.56      inference('clc', [status(thm)], ['63', '64'])).
% 0.39/0.56  thf('66', plain,
% 0.39/0.56      (((v2_struct_0 @ sk_A)
% 0.39/0.56        | (v7_struct_0 @ sk_A)
% 0.39/0.56        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.39/0.56        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.39/0.56      inference('demod', [status(thm)], ['57', '58', '65'])).
% 0.39/0.56  thf('67', plain,
% 0.39/0.56      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.39/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.39/0.56      inference('split', [status(esa)], ['0'])).
% 0.39/0.56  thf('68', plain,
% 0.39/0.56      ((((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.39/0.56         | (v7_struct_0 @ sk_A)
% 0.39/0.56         | (v2_struct_0 @ sk_A)))
% 0.39/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['66', '67'])).
% 0.39/0.56  thf('69', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.39/0.56      inference('clc', [status(thm)], ['47', '48'])).
% 0.39/0.56  thf('70', plain,
% 0.39/0.56      ((((v2_struct_0 @ sk_A) | (v7_struct_0 @ sk_A)))
% 0.39/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.39/0.56      inference('clc', [status(thm)], ['68', '69'])).
% 0.39/0.56  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('72', plain,
% 0.39/0.56      (((v7_struct_0 @ sk_A))
% 0.39/0.56         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.39/0.56      inference('clc', [status(thm)], ['70', '71'])).
% 0.39/0.56  thf('73', plain,
% 0.39/0.56      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56         (u1_struct_0 @ sk_A)))
% 0.39/0.56         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56               (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('split', [status(esa)], ['29'])).
% 0.39/0.56  thf(t8_tex_2, axiom,
% 0.39/0.56    (![A:$i]:
% 0.39/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.39/0.56       ( ![B:$i]:
% 0.39/0.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.56           ( ~( ( v1_subset_1 @
% 0.39/0.56                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.39/0.56                  ( u1_struct_0 @ A ) ) & 
% 0.39/0.56                ( v7_struct_0 @ A ) ) ) ) ) ))).
% 0.39/0.56  thf('74', plain,
% 0.39/0.56      (![X26 : $i, X27 : $i]:
% 0.39/0.56         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 0.39/0.56          | ~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X27) @ X26) @ 
% 0.39/0.56               (u1_struct_0 @ X27))
% 0.39/0.56          | ~ (v7_struct_0 @ X27)
% 0.39/0.56          | ~ (l1_struct_0 @ X27)
% 0.39/0.56          | (v2_struct_0 @ X27))),
% 0.39/0.56      inference('cnf', [status(esa)], [t8_tex_2])).
% 0.39/0.56  thf('75', plain,
% 0.39/0.56      ((((v2_struct_0 @ sk_A)
% 0.39/0.56         | ~ (l1_struct_0 @ sk_A)
% 0.39/0.56         | ~ (v7_struct_0 @ sk_A)
% 0.39/0.56         | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.39/0.56         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56               (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('sup-', [status(thm)], ['73', '74'])).
% 0.39/0.56  thf('76', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.56  thf('77', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('78', plain,
% 0.39/0.56      ((((v2_struct_0 @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 0.39/0.56         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56               (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.39/0.56  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('80', plain,
% 0.39/0.56      ((~ (v7_struct_0 @ sk_A))
% 0.39/0.56         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56               (u1_struct_0 @ sk_A))))),
% 0.39/0.56      inference('clc', [status(thm)], ['78', '79'])).
% 0.39/0.56  thf('81', plain,
% 0.39/0.56      (~
% 0.39/0.56       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.39/0.56         (u1_struct_0 @ sk_A))) | 
% 0.39/0.56       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.39/0.56      inference('sup-', [status(thm)], ['72', '80'])).
% 0.39/0.56  thf('82', plain, ($false),
% 0.39/0.56      inference('sat_resolution*', [status(thm)], ['1', '53', '54', '81'])).
% 0.39/0.56  
% 0.39/0.56  % SZS output end Refutation
% 0.39/0.56  
% 0.39/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
