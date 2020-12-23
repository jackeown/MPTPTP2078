%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lmFmJ0htIV

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:59 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 309 expanded)
%              Number of leaves         :   28 (  96 expanded)
%              Depth                    :   27
%              Number of atoms          : 1023 (4406 expanded)
%              Number of equality atoms :   13 (  34 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(t10_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m2_connsp_2 @ C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
              <=> ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( m2_connsp_2 @ C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
                <=> ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t10_connsp_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( X5 != X4 )
      | ( r2_hidden @ X5 @ X6 )
      | ( X6
       != ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X4: $i] :
      ( r2_hidden @ X4 @ ( k1_tarski @ X4 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ X19 )
      | ( ( k6_domain_1 @ X19 @ X20 )
        = ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('6',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('9',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(d2_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m2_connsp_2 @ C @ A @ B )
              <=> ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m2_connsp_2 @ X26 @ X25 @ X24 )
      | ( r1_tarski @ X24 @ ( k1_tops_1 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ~ ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('18',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('19',plain,
    ( ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B )
    | ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( ( ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf('22',plain,
    ( ~ ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B )
    | ~ ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B )
    | ~ ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['19'])).

thf('25',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_connsp_2 @ X23 @ X22 @ X21 )
      | ( r2_hidden @ X21 @ ( k1_tops_1 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_2 ) )
      | ~ ( m1_connsp_2 @ sk_C_2 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_2 ) )
      | ~ ( m1_connsp_2 @ sk_C_2 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_2 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_2 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_2 ) )
   <= ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['33','34'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( X7 = X4 )
      | ( X6
       != ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('38',plain,(
    ! [X4: $i,X7: $i] :
      ( ( X7 = X4 )
      | ~ ( r2_hidden @ X7 @ ( k1_tarski @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_2 ) )
   <= ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('45',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( r1_tarski @ X24 @ ( k1_tops_1 @ X25 @ X26 ) )
      | ( m2_connsp_2 @ X26 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['43','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('54',plain,
    ( ~ ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ~ ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['22'])).

thf('55',plain,
    ( ( ~ ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('58',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('59',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('61',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('62',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['19'])).

thf('67',plain,(
    m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['23','65','66'])).

thf('68',plain,
    ( ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['21','67'])).

thf('69',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['17','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r2_hidden @ X21 @ ( k1_tops_1 @ X22 @ X23 ) )
      | ( m1_connsp_2 @ X23 @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C_2 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C_2 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['22'])).

thf('83',plain,(
    ~ ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['23','65'])).

thf('84',plain,(
    ~ ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['81','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf('91',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['0','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lmFmJ0htIV
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:39:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.41/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.61  % Solved by: fo/fo7.sh
% 0.41/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.61  % done 312 iterations in 0.152s
% 0.41/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.61  % SZS output start Refutation
% 0.41/0.61  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.41/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.61  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.41/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.61  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.41/0.61  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.41/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.41/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.61  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.41/0.61  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.41/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.61  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.41/0.61  thf(t10_connsp_2, conjecture,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.61           ( ![C:$i]:
% 0.41/0.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.61               ( ( m2_connsp_2 @
% 0.41/0.61                   C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.41/0.61                 ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ))).
% 0.41/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.61    (~( ![A:$i]:
% 0.41/0.61        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.41/0.61            ( l1_pre_topc @ A ) ) =>
% 0.41/0.61          ( ![B:$i]:
% 0.41/0.61            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.61              ( ![C:$i]:
% 0.41/0.61                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.61                  ( ( m2_connsp_2 @
% 0.41/0.61                      C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.41/0.61                    ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ) )),
% 0.41/0.61    inference('cnf.neg', [status(esa)], [t10_connsp_2])).
% 0.41/0.61  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(d1_tarski, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.41/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.41/0.61  thf('1', plain,
% 0.41/0.61      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.41/0.61         (((X5) != (X4)) | (r2_hidden @ X5 @ X6) | ((X6) != (k1_tarski @ X4)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d1_tarski])).
% 0.41/0.61  thf('2', plain, (![X4 : $i]: (r2_hidden @ X4 @ (k1_tarski @ X4))),
% 0.41/0.61      inference('simplify', [status(thm)], ['1'])).
% 0.41/0.61  thf('3', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('4', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(redefinition_k6_domain_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.41/0.61       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.41/0.61  thf('5', plain,
% 0.41/0.61      (![X19 : $i, X20 : $i]:
% 0.41/0.61         ((v1_xboole_0 @ X19)
% 0.41/0.61          | ~ (m1_subset_1 @ X20 @ X19)
% 0.41/0.61          | ((k6_domain_1 @ X19 @ X20) = (k1_tarski @ X20)))),
% 0.41/0.61      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.41/0.61  thf('6', plain,
% 0.41/0.61      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.41/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.61  thf('7', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(dt_k6_domain_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.41/0.61       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.41/0.61  thf('8', plain,
% 0.41/0.61      (![X17 : $i, X18 : $i]:
% 0.41/0.61         ((v1_xboole_0 @ X17)
% 0.41/0.61          | ~ (m1_subset_1 @ X18 @ X17)
% 0.41/0.61          | (m1_subset_1 @ (k6_domain_1 @ X17 @ X18) @ (k1_zfmisc_1 @ X17)))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.41/0.61  thf('9', plain,
% 0.41/0.61      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.41/0.61         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.61  thf('10', plain,
% 0.41/0.61      (((m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.41/0.61         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('sup+', [status(thm)], ['6', '9'])).
% 0.41/0.61  thf('11', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.41/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.61      inference('simplify', [status(thm)], ['10'])).
% 0.41/0.61  thf(d2_connsp_2, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.61           ( ![C:$i]:
% 0.41/0.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.61               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.41/0.61                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.41/0.61  thf('12', plain,
% 0.41/0.61      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.41/0.61          | ~ (m2_connsp_2 @ X26 @ X25 @ X24)
% 0.41/0.61          | (r1_tarski @ X24 @ (k1_tops_1 @ X25 @ X26))
% 0.41/0.61          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.41/0.61          | ~ (l1_pre_topc @ X25)
% 0.41/0.61          | ~ (v2_pre_topc @ X25))),
% 0.41/0.61      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.41/0.61  thf('13', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.41/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.61          | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.41/0.61          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.61  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('16', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.61          | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.41/0.61          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.41/0.61      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.41/0.61  thf('17', plain,
% 0.41/0.61      ((~ (m2_connsp_2 @ sk_C_2 @ sk_A @ (k1_tarski @ sk_B))
% 0.41/0.61        | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C_2))
% 0.41/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['3', '16'])).
% 0.41/0.61  thf('18', plain,
% 0.41/0.61      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.41/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.61  thf('19', plain,
% 0.41/0.61      (((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B)
% 0.41/0.61        | (m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.41/0.61           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('20', plain,
% 0.41/0.61      (((m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.41/0.61         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.41/0.61         <= (((m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.41/0.61               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.41/0.61      inference('split', [status(esa)], ['19'])).
% 0.41/0.61  thf('21', plain,
% 0.41/0.61      ((((m2_connsp_2 @ sk_C_2 @ sk_A @ (k1_tarski @ sk_B))
% 0.41/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.41/0.61         <= (((m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.41/0.61               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.41/0.61      inference('sup+', [status(thm)], ['18', '20'])).
% 0.41/0.61  thf('22', plain,
% 0.41/0.61      ((~ (m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B)
% 0.41/0.61        | ~ (m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.41/0.61             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('23', plain,
% 0.41/0.61      (~ ((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B)) | 
% 0.41/0.61       ~
% 0.41/0.61       ((m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.41/0.61         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('split', [status(esa)], ['22'])).
% 0.41/0.61  thf('24', plain,
% 0.41/0.61      (((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B))
% 0.41/0.61         <= (((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('split', [status(esa)], ['19'])).
% 0.41/0.61  thf('25', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(d1_connsp_2, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.61       ( ![B:$i]:
% 0.41/0.61         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.41/0.61           ( ![C:$i]:
% 0.41/0.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.61               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.41/0.61                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.41/0.61  thf('26', plain,
% 0.41/0.61      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.41/0.61          | ~ (m1_connsp_2 @ X23 @ X22 @ X21)
% 0.41/0.61          | (r2_hidden @ X21 @ (k1_tops_1 @ X22 @ X23))
% 0.41/0.61          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.41/0.61          | ~ (l1_pre_topc @ X22)
% 0.41/0.61          | ~ (v2_pre_topc @ X22)
% 0.41/0.61          | (v2_struct_0 @ X22))),
% 0.41/0.61      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.41/0.61  thf('27', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_A)
% 0.41/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.41/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.41/0.61          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_2))
% 0.41/0.61          | ~ (m1_connsp_2 @ sk_C_2 @ sk_A @ X0)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['25', '26'])).
% 0.41/0.61  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('30', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_A)
% 0.41/0.61          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_2))
% 0.41/0.61          | ~ (m1_connsp_2 @ sk_C_2 @ sk_A @ X0)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.41/0.61  thf('31', plain,
% 0.41/0.61      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.41/0.61         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_2))
% 0.41/0.61         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['24', '30'])).
% 0.41/0.61  thf('32', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('33', plain,
% 0.41/0.61      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_2))
% 0.41/0.61         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('demod', [status(thm)], ['31', '32'])).
% 0.41/0.61  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('35', plain,
% 0.41/0.61      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_2)))
% 0.41/0.61         <= (((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('clc', [status(thm)], ['33', '34'])).
% 0.41/0.61  thf(d3_tarski, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( r1_tarski @ A @ B ) <=>
% 0.41/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.41/0.61  thf('36', plain,
% 0.41/0.61      (![X1 : $i, X3 : $i]:
% 0.41/0.61         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.61  thf('37', plain,
% 0.41/0.61      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X7 @ X6) | ((X7) = (X4)) | ((X6) != (k1_tarski @ X4)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d1_tarski])).
% 0.41/0.61  thf('38', plain,
% 0.41/0.61      (![X4 : $i, X7 : $i]:
% 0.41/0.61         (((X7) = (X4)) | ~ (r2_hidden @ X7 @ (k1_tarski @ X4)))),
% 0.41/0.61      inference('simplify', [status(thm)], ['37'])).
% 0.41/0.61  thf('39', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.41/0.61          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['36', '38'])).
% 0.41/0.61  thf('40', plain,
% 0.41/0.61      (![X1 : $i, X3 : $i]:
% 0.41/0.61         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.61  thf('41', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X0 @ X1)
% 0.41/0.61          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.41/0.61          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['39', '40'])).
% 0.41/0.61  thf('42', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.41/0.61      inference('simplify', [status(thm)], ['41'])).
% 0.41/0.61  thf('43', plain,
% 0.41/0.61      (((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C_2)))
% 0.41/0.61         <= (((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['35', '42'])).
% 0.41/0.61  thf('44', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.41/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.41/0.61      inference('simplify', [status(thm)], ['10'])).
% 0.41/0.61  thf('45', plain,
% 0.41/0.61      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.41/0.61          | ~ (r1_tarski @ X24 @ (k1_tops_1 @ X25 @ X26))
% 0.41/0.61          | (m2_connsp_2 @ X26 @ X25 @ X24)
% 0.41/0.61          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.41/0.61          | ~ (l1_pre_topc @ X25)
% 0.41/0.61          | ~ (v2_pre_topc @ X25))),
% 0.41/0.61      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.41/0.61  thf('46', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.41/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.61          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.41/0.61          | ~ (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['44', '45'])).
% 0.41/0.61  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('49', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.61          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.41/0.61          | ~ (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.41/0.61      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.41/0.61  thf('50', plain,
% 0.41/0.61      ((((m2_connsp_2 @ sk_C_2 @ sk_A @ (k1_tarski @ sk_B))
% 0.41/0.61         | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.41/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.41/0.61         <= (((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['43', '49'])).
% 0.41/0.61  thf('51', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('52', plain,
% 0.41/0.61      ((((m2_connsp_2 @ sk_C_2 @ sk_A @ (k1_tarski @ sk_B))
% 0.41/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.41/0.61         <= (((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('demod', [status(thm)], ['50', '51'])).
% 0.41/0.61  thf('53', plain,
% 0.41/0.61      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.41/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.61  thf('54', plain,
% 0.41/0.61      ((~ (m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.41/0.61           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.41/0.61         <= (~
% 0.41/0.61             ((m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.41/0.61               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.41/0.61      inference('split', [status(esa)], ['22'])).
% 0.41/0.61  thf('55', plain,
% 0.41/0.61      (((~ (m2_connsp_2 @ sk_C_2 @ sk_A @ (k1_tarski @ sk_B))
% 0.41/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.41/0.61         <= (~
% 0.41/0.61             ((m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.41/0.61               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['53', '54'])).
% 0.41/0.61  thf('56', plain,
% 0.41/0.61      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.41/0.61         <= (~
% 0.41/0.61             ((m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.41/0.61               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.41/0.61             ((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['52', '55'])).
% 0.41/0.61  thf('57', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.41/0.61         <= (~
% 0.41/0.61             ((m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.41/0.61               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.41/0.61             ((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('simplify', [status(thm)], ['56'])).
% 0.41/0.61  thf(fc2_struct_0, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.41/0.61       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.41/0.61  thf('58', plain,
% 0.41/0.61      (![X16 : $i]:
% 0.41/0.61         (~ (v1_xboole_0 @ (u1_struct_0 @ X16))
% 0.41/0.61          | ~ (l1_struct_0 @ X16)
% 0.41/0.61          | (v2_struct_0 @ X16))),
% 0.41/0.61      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.41/0.61  thf('59', plain,
% 0.41/0.61      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.41/0.61         <= (~
% 0.41/0.61             ((m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.41/0.61               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.41/0.61             ((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['57', '58'])).
% 0.41/0.61  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(dt_l1_pre_topc, axiom,
% 0.41/0.61    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.41/0.61  thf('61', plain,
% 0.41/0.61      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.41/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.61  thf('62', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.61      inference('sup-', [status(thm)], ['60', '61'])).
% 0.41/0.61  thf('63', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_A))
% 0.41/0.61         <= (~
% 0.41/0.61             ((m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.41/0.61               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.41/0.61             ((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('demod', [status(thm)], ['59', '62'])).
% 0.41/0.61  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('65', plain,
% 0.41/0.61      (((m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.41/0.61         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) | 
% 0.41/0.61       ~ ((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['63', '64'])).
% 0.41/0.61  thf('66', plain,
% 0.41/0.61      (((m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.41/0.61         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) | 
% 0.41/0.61       ((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B))),
% 0.41/0.61      inference('split', [status(esa)], ['19'])).
% 0.41/0.61  thf('67', plain,
% 0.41/0.61      (((m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.41/0.61         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.41/0.61      inference('sat_resolution*', [status(thm)], ['23', '65', '66'])).
% 0.41/0.61  thf('68', plain,
% 0.41/0.61      (((m2_connsp_2 @ sk_C_2 @ sk_A @ (k1_tarski @ sk_B))
% 0.41/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('simpl_trail', [status(thm)], ['21', '67'])).
% 0.41/0.61  thf('69', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61        | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C_2)))),
% 0.41/0.61      inference('clc', [status(thm)], ['17', '68'])).
% 0.41/0.61  thf('70', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X0 @ X1)
% 0.41/0.61          | (r2_hidden @ X0 @ X2)
% 0.41/0.61          | ~ (r1_tarski @ X1 @ X2))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.61  thf('71', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_2))
% 0.41/0.61          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['69', '70'])).
% 0.41/0.61  thf('72', plain,
% 0.41/0.61      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_2))
% 0.41/0.61        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['2', '71'])).
% 0.41/0.61  thf('73', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('74', plain,
% 0.41/0.61      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.41/0.61          | ~ (r2_hidden @ X21 @ (k1_tops_1 @ X22 @ X23))
% 0.41/0.61          | (m1_connsp_2 @ X23 @ X22 @ X21)
% 0.41/0.61          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.41/0.61          | ~ (l1_pre_topc @ X22)
% 0.41/0.61          | ~ (v2_pre_topc @ X22)
% 0.41/0.61          | (v2_struct_0 @ X22))),
% 0.41/0.61      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.41/0.61  thf('75', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_A)
% 0.41/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.41/0.61          | ~ (l1_pre_topc @ sk_A)
% 0.41/0.61          | (m1_connsp_2 @ sk_C_2 @ sk_A @ X0)
% 0.41/0.61          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_2))
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['73', '74'])).
% 0.41/0.61  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('78', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v2_struct_0 @ sk_A)
% 0.41/0.61          | (m1_connsp_2 @ sk_C_2 @ sk_A @ X0)
% 0.41/0.61          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_2))
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.41/0.61  thf('79', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.41/0.61        | (m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B)
% 0.41/0.61        | (v2_struct_0 @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['72', '78'])).
% 0.41/0.61  thf('80', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('81', plain,
% 0.41/0.61      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.41/0.61        | (m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B)
% 0.41/0.61        | (v2_struct_0 @ sk_A))),
% 0.41/0.61      inference('demod', [status(thm)], ['79', '80'])).
% 0.41/0.61  thf('82', plain,
% 0.41/0.61      ((~ (m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B))
% 0.41/0.61         <= (~ ((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('split', [status(esa)], ['22'])).
% 0.41/0.61  thf('83', plain, (~ ((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B))),
% 0.41/0.61      inference('sat_resolution*', [status(thm)], ['23', '65'])).
% 0.41/0.61  thf('84', plain, (~ (m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B)),
% 0.41/0.61      inference('simpl_trail', [status(thm)], ['82', '83'])).
% 0.41/0.61  thf('85', plain,
% 0.41/0.61      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.61      inference('clc', [status(thm)], ['81', '84'])).
% 0.41/0.61  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('87', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.41/0.61      inference('clc', [status(thm)], ['85', '86'])).
% 0.41/0.61  thf('88', plain,
% 0.41/0.61      (![X16 : $i]:
% 0.41/0.61         (~ (v1_xboole_0 @ (u1_struct_0 @ X16))
% 0.41/0.61          | ~ (l1_struct_0 @ X16)
% 0.41/0.61          | (v2_struct_0 @ X16))),
% 0.41/0.61      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.41/0.61  thf('89', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['87', '88'])).
% 0.41/0.61  thf('90', plain, ((l1_struct_0 @ sk_A)),
% 0.41/0.61      inference('sup-', [status(thm)], ['60', '61'])).
% 0.41/0.61  thf('91', plain, ((v2_struct_0 @ sk_A)),
% 0.41/0.61      inference('demod', [status(thm)], ['89', '90'])).
% 0.41/0.61  thf('92', plain, ($false), inference('demod', [status(thm)], ['0', '91'])).
% 0.41/0.61  
% 0.41/0.61  % SZS output end Refutation
% 0.41/0.61  
% 0.44/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
