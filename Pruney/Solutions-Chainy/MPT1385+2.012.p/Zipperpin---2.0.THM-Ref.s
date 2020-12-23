%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ihxbSeF5dA

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 601 expanded)
%              Number of leaves         :   34 ( 181 expanded)
%              Depth                    :   30
%              Number of atoms          : 1472 (8880 expanded)
%              Number of equality atoms :    9 (  19 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ X12 )
      | ( ( k6_domain_1 @ X12 @ X13 )
        = ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('4',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_connsp_2 @ X16 @ X15 @ X14 )
      | ( r2_hidden @ X14 @ ( k1_tops_1 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['19','20'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('22',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('23',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( m1_connsp_2 @ B @ A @ C )
               => ( r2_hidden @ C @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( m1_connsp_2 @ X28 @ X29 @ X30 )
      | ( r2_hidden @ X30 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['24','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('37',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('40',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X7 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('41',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

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

thf('42',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( r1_tarski @ X17 @ ( k1_tops_1 @ X18 @ X19 ) )
      | ( m2_connsp_2 @ X19 @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
        | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
        | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['23','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( m1_subset_1 @ sk_B @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('54',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('55',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ X12 )
      | ( ( k6_domain_1 @ X12 @ X13 )
        = ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('58',plain,
    ( ( ( k6_domain_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('60',plain,
    ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf('61',plain,
    ( ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['53','54'])).

thf('64',plain,
    ( ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) )
   <= ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
   <= ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','64'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('66',plain,(
    ! [X11: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('67',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['53','54'])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('73',plain,(
    m2_connsp_2 @ sk_C_1 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['9','71','72'])).

thf('74',plain,
    ( ( m2_connsp_2 @ sk_C_1 @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['7','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(existence_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ? [C: $i] :
          ( m1_connsp_2 @ C @ A @ B ) ) )).

thf('76',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ( m1_connsp_2 @ ( sk_C @ X27 @ X26 ) @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[existence_m1_connsp_2])).

thf('77',plain,
    ( ( m1_connsp_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( m1_connsp_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_connsp_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    m1_connsp_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['80','81'])).

thf('84',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('85',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_connsp_2 @ X22 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','91'])).

thf('93',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( m1_connsp_2 @ X28 @ X29 @ X30 )
      | ( r2_hidden @ X30 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t6_connsp_2])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_connsp_2 @ ( sk_C @ sk_B @ sk_A ) @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,
    ( ( r2_hidden @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['82','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( r2_hidden @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    r2_hidden @ sk_B @ ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','91'])).

thf('104',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X7 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('108',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m2_connsp_2 @ X19 @ X18 @ X17 )
      | ( r1_tarski @ X17 @ ( k1_tops_1 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf(dt_m2_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ! [C: $i] :
          ( ( m2_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('115',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( m2_connsp_2 @ X25 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_connsp_2])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['116','117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['113','119'])).

thf('121',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['74','120'])).

thf('122',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('123',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r2_hidden @ X14 @ ( k1_tops_1 @ X15 @ X16 ) )
      | ( m1_connsp_2 @ X16 @ X15 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['123','129'])).

thf('131',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('134',plain,(
    ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['9','71'])).

thf('135',plain,(
    ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['132','135'])).

thf('137',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','138'])).

thf('140',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['53','54'])).

thf('141',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X11: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('143',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['53','54'])).

thf('145',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    $false ),
    inference(demod,[status(thm)],['0','145'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ihxbSeF5dA
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:54:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 213 iterations in 0.074s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.52  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.20/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.52  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.20/0.52  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.52  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(t10_connsp_2, conjecture,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52               ( ( m2_connsp_2 @
% 0.20/0.52                   C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.20/0.52                 ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i]:
% 0.20/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.52            ( l1_pre_topc @ A ) ) =>
% 0.20/0.52          ( ![B:$i]:
% 0.20/0.52            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.52              ( ![C:$i]:
% 0.20/0.52                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52                  ( ( m2_connsp_2 @
% 0.20/0.52                      C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.20/0.52                    ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t10_connsp_2])).
% 0.20/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d3_struct_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X9 : $i]:
% 0.20/0.52         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.52  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.52       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ X12)
% 0.20/0.52          | ~ (m1_subset_1 @ X13 @ X12)
% 0.20/0.52          | ((k6_domain_1 @ X12 @ X13) = (k1_tarski @ X13)))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.20/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.20/0.52        | (m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.52           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.52         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.20/0.52         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.52               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.52      inference('split', [status(esa)], ['5'])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      ((((m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.52         <= (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.52               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['4', '6'])).
% 0.20/0.52  thf('8', plain,
% 0.20/0.52      ((~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.20/0.52        | ~ (m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.52             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)) | 
% 0.20/0.52       ~
% 0.20/0.52       ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.52         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['8'])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.20/0.52         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['5'])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d1_connsp_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.20/0.52                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.20/0.52          | ~ (m1_connsp_2 @ X16 @ X15 @ X14)
% 0.20/0.52          | (r2_hidden @ X14 @ (k1_tops_1 @ X15 @ X16))
% 0.20/0.52          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.52          | ~ (l1_pre_topc @ X15)
% 0.20/0.52          | ~ (v2_pre_topc @ X15)
% 0.20/0.52          | (v2_struct_0 @ X15))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.52          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('14', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.52          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.52         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.52         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['10', '16'])).
% 0.20/0.52  thf('18', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.52         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.52  thf('20', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.20/0.52         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('clc', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf(l1_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ (k1_tarski @ X1) @ X3) | ~ (r2_hidden @ X1 @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.20/0.52         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.20/0.52         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('split', [status(esa)], ['5'])).
% 0.20/0.52  thf('25', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(t6_connsp_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.52               ( ( m1_connsp_2 @ B @ A @ C ) => ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.20/0.52          | ~ (m1_connsp_2 @ X28 @ X29 @ X30)
% 0.20/0.52          | (r2_hidden @ X30 @ X28)
% 0.20/0.52          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 0.20/0.52          | ~ (l1_pre_topc @ X29)
% 0.20/0.52          | ~ (v2_pre_topc @ X29)
% 0.20/0.52          | (v2_struct_0 @ X29))),
% 0.20/0.52      inference('cnf', [status(esa)], [t6_connsp_2])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (r2_hidden @ X0 @ sk_C_1)
% 0.20/0.52          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.52  thf('29', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (r2_hidden @ X0 @ sk_C_1)
% 0.20/0.52          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.20/0.52  thf('32', plain,
% 0.20/0.52      ((~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.20/0.52        | (r2_hidden @ sk_B @ sk_C_1)
% 0.20/0.52        | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['25', '31'])).
% 0.20/0.52  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('34', plain,
% 0.20/0.52      (((r2_hidden @ sk_B @ sk_C_1) | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.20/0.52      inference('clc', [status(thm)], ['32', '33'])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (((r2_hidden @ sk_B @ sk_C_1))
% 0.20/0.52         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['24', '34'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(l3_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X4 @ X5)
% 0.20/0.52          | (r2_hidden @ X4 @ X6)
% 0.20/0.52          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.20/0.52      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.20/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (((r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.20/0.52         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['35', '38'])).
% 0.20/0.52  thf(t63_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r2_hidden @ A @ B ) =>
% 0.20/0.52       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (k1_tarski @ X7) @ (k1_zfmisc_1 @ X8))
% 0.20/0.52          | ~ (r2_hidden @ X7 @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      (((m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.20/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.52         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.52  thf(d2_connsp_2, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.52       ( ![B:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52           ( ![C:$i]:
% 0.20/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.20/0.52                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.52          | ~ (r1_tarski @ X17 @ (k1_tops_1 @ X18 @ X19))
% 0.20/0.52          | (m2_connsp_2 @ X19 @ X18 @ X17)
% 0.20/0.52          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.52          | ~ (l1_pre_topc @ X18)
% 0.20/0.52          | ~ (v2_pre_topc @ X18))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          (~ (v2_pre_topc @ sk_A)
% 0.20/0.52           | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52           | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.52           | ~ (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0))))
% 0.20/0.52         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.52  thf('44', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52           | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.52           | ~ (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0))))
% 0.20/0.52         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      ((((m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.52         | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.20/0.52         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['23', '46'])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('49', plain,
% 0.20/0.52      (((m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B)))
% 0.20/0.52         <= (((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.52  thf('50', plain,
% 0.20/0.52      (![X9 : $i]:
% 0.20/0.52         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.52  thf('51', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('52', plain,
% 0.20/0.52      (((m1_subset_1 @ sk_B @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup+', [status(thm)], ['50', '51'])).
% 0.20/0.52  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_l1_pre_topc, axiom,
% 0.20/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.52  thf('54', plain,
% 0.20/0.52      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.52  thf('55', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.52  thf('56', plain, ((m1_subset_1 @ sk_B @ (k2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['52', '55'])).
% 0.20/0.52  thf('57', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         ((v1_xboole_0 @ X12)
% 0.20/0.52          | ~ (m1_subset_1 @ X13 @ X12)
% 0.20/0.52          | ((k6_domain_1 @ X12 @ X13) = (k1_tarski @ X13)))),
% 0.20/0.52      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.52  thf('58', plain,
% 0.20/0.52      ((((k6_domain_1 @ (k2_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.20/0.52        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.52  thf('59', plain,
% 0.20/0.52      (![X9 : $i]:
% 0.20/0.52         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.52  thf('60', plain,
% 0.20/0.52      ((~ (m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.52           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.20/0.52         <= (~
% 0.20/0.52             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.52               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.52      inference('split', [status(esa)], ['8'])).
% 0.20/0.52  thf('61', plain,
% 0.20/0.52      (((~ (m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.52            (k6_domain_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.20/0.52         | ~ (l1_struct_0 @ sk_A)))
% 0.20/0.52         <= (~
% 0.20/0.52             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.52               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.52  thf('62', plain,
% 0.20/0.52      (((~ (m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.52         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.20/0.52         | ~ (l1_struct_0 @ sk_A)))
% 0.20/0.52         <= (~
% 0.20/0.52             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.52               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['58', '61'])).
% 0.20/0.52  thf('63', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.52  thf('64', plain,
% 0.20/0.52      (((~ (m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.52         | (v1_xboole_0 @ (k2_struct_0 @ sk_A))))
% 0.20/0.52         <= (~
% 0.20/0.52             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.52               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.20/0.52      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.52  thf('65', plain,
% 0.20/0.52      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)))
% 0.20/0.52         <= (~
% 0.20/0.52             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.52               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.20/0.52             ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['49', '64'])).
% 0.20/0.52  thf(fc5_struct_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.52       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.20/0.52  thf('66', plain,
% 0.20/0.52      (![X11 : $i]:
% 0.20/0.52         (~ (v1_xboole_0 @ (k2_struct_0 @ X11))
% 0.20/0.52          | ~ (l1_struct_0 @ X11)
% 0.20/0.52          | (v2_struct_0 @ X11))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.20/0.52  thf('67', plain,
% 0.20/0.52      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.20/0.52         <= (~
% 0.20/0.52             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.52               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.20/0.52             ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.52  thf('68', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.52      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.52  thf('69', plain,
% 0.20/0.52      (((v2_struct_0 @ sk_A))
% 0.20/0.52         <= (~
% 0.20/0.52             ((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.52               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.20/0.52             ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['67', '68'])).
% 0.20/0.52  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('71', plain,
% 0.20/0.52      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.52         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) | 
% 0.20/0.52       ~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.52  thf('72', plain,
% 0.20/0.52      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.52         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) | 
% 0.20/0.52       ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.20/0.52      inference('split', [status(esa)], ['5'])).
% 0.20/0.52  thf('73', plain,
% 0.20/0.52      (((m2_connsp_2 @ sk_C_1 @ sk_A @ 
% 0.20/0.52         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['9', '71', '72'])).
% 0.20/0.52  thf('74', plain,
% 0.20/0.52      (((m2_connsp_2 @ sk_C_1 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['7', '73'])).
% 0.20/0.52  thf('75', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(existence_m1_connsp_2, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.52         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52       ( ?[C:$i]: ( m1_connsp_2 @ C @ A @ B ) ) ))).
% 0.20/0.52  thf('76', plain,
% 0.20/0.52      (![X26 : $i, X27 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X26)
% 0.20/0.52          | ~ (v2_pre_topc @ X26)
% 0.20/0.52          | (v2_struct_0 @ X26)
% 0.20/0.52          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 0.20/0.52          | (m1_connsp_2 @ (sk_C @ X27 @ X26) @ X26 @ X27))),
% 0.20/0.52      inference('cnf', [status(esa)], [existence_m1_connsp_2])).
% 0.20/0.52  thf('77', plain,
% 0.20/0.52      (((m1_connsp_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ sk_B)
% 0.20/0.52        | (v2_struct_0 @ sk_A)
% 0.20/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['75', '76'])).
% 0.20/0.52  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('80', plain,
% 0.20/0.52      (((m1_connsp_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ sk_B)
% 0.20/0.52        | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.20/0.52  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('82', plain, ((m1_connsp_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ sk_B)),
% 0.20/0.52      inference('clc', [status(thm)], ['80', '81'])).
% 0.20/0.52  thf('83', plain, ((m1_connsp_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ sk_B)),
% 0.20/0.52      inference('clc', [status(thm)], ['80', '81'])).
% 0.20/0.52  thf('84', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(dt_m1_connsp_2, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.52         ( l1_pre_topc @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.52       ( ![C:$i]:
% 0.20/0.52         ( ( m1_connsp_2 @ C @ A @ B ) =>
% 0.20/0.52           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('85', plain,
% 0.20/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X20)
% 0.20/0.52          | ~ (v2_pre_topc @ X20)
% 0.20/0.52          | (v2_struct_0 @ X20)
% 0.20/0.52          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.20/0.52          | (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.20/0.52          | ~ (m1_connsp_2 @ X22 @ X20 @ X21))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_m1_connsp_2])).
% 0.20/0.52  thf('86', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.52          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | (v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52          | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['84', '85'])).
% 0.20/0.52  thf('87', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('89', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m1_connsp_2 @ X0 @ sk_A @ sk_B)
% 0.20/0.52          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.20/0.52  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('91', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | ~ (m1_connsp_2 @ X0 @ sk_A @ sk_B))),
% 0.20/0.52      inference('clc', [status(thm)], ['89', '90'])).
% 0.20/0.52  thf('92', plain,
% 0.20/0.52      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['83', '91'])).
% 0.20/0.52  thf('93', plain,
% 0.20/0.52      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.20/0.52          | ~ (m1_connsp_2 @ X28 @ X29 @ X30)
% 0.20/0.52          | (r2_hidden @ X30 @ X28)
% 0.20/0.52          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X29))
% 0.20/0.52          | ~ (l1_pre_topc @ X29)
% 0.20/0.52          | ~ (v2_pre_topc @ X29)
% 0.20/0.52          | (v2_struct_0 @ X29))),
% 0.20/0.52      inference('cnf', [status(esa)], [t6_connsp_2])).
% 0.20/0.52  thf('94', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (r2_hidden @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.52          | ~ (m1_connsp_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['92', '93'])).
% 0.20/0.52  thf('95', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('97', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((v2_struct_0 @ sk_A)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | (r2_hidden @ X0 @ (sk_C @ sk_B @ sk_A))
% 0.20/0.52          | ~ (m1_connsp_2 @ (sk_C @ sk_B @ sk_A) @ sk_A @ X0))),
% 0.20/0.52      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.20/0.52  thf('98', plain,
% 0.20/0.52      (((r2_hidden @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.20/0.52        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['82', '97'])).
% 0.20/0.52  thf('99', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('100', plain,
% 0.20/0.52      (((r2_hidden @ sk_B @ (sk_C @ sk_B @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.20/0.52      inference('demod', [status(thm)], ['98', '99'])).
% 0.20/0.52  thf('101', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('102', plain, ((r2_hidden @ sk_B @ (sk_C @ sk_B @ sk_A))),
% 0.20/0.52      inference('clc', [status(thm)], ['100', '101'])).
% 0.20/0.52  thf('103', plain,
% 0.20/0.52      ((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ 
% 0.20/0.52        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['83', '91'])).
% 0.20/0.52  thf('104', plain,
% 0.20/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X4 @ X5)
% 0.20/0.52          | (r2_hidden @ X4 @ X6)
% 0.20/0.52          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.20/0.52      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.52  thf('105', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ (sk_C @ sk_B @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['103', '104'])).
% 0.20/0.52  thf('106', plain, ((r2_hidden @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['102', '105'])).
% 0.20/0.52  thf('107', plain,
% 0.20/0.52      (![X7 : $i, X8 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (k1_tarski @ X7) @ (k1_zfmisc_1 @ X8))
% 0.20/0.52          | ~ (r2_hidden @ X7 @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.20/0.52  thf('108', plain,
% 0.20/0.52      ((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['106', '107'])).
% 0.20/0.52  thf('109', plain,
% 0.20/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.52          | ~ (m2_connsp_2 @ X19 @ X18 @ X17)
% 0.20/0.52          | (r1_tarski @ X17 @ (k1_tops_1 @ X18 @ X19))
% 0.20/0.52          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.52          | ~ (l1_pre_topc @ X18)
% 0.20/0.52          | ~ (v2_pre_topc @ X18))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.20/0.52  thf('110', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (v2_pre_topc @ sk_A)
% 0.20/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.52          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['108', '109'])).
% 0.20/0.52  thf('111', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('113', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.20/0.52          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.20/0.52      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.20/0.52  thf('114', plain,
% 0.20/0.52      ((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['106', '107'])).
% 0.20/0.52  thf(dt_m2_connsp_2, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.20/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.52       ( ![C:$i]:
% 0.20/0.52         ( ( m2_connsp_2 @ C @ A @ B ) =>
% 0.20/0.52           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.52  thf('115', plain,
% 0.20/0.52      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.52         (~ (l1_pre_topc @ X23)
% 0.20/0.52          | ~ (v2_pre_topc @ X23)
% 0.20/0.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.20/0.52          | (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.20/0.52          | ~ (m2_connsp_2 @ X25 @ X23 @ X24))),
% 0.20/0.52      inference('cnf', [status(esa)], [dt_m2_connsp_2])).
% 0.20/0.52  thf('116', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.52          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.52          | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['114', '115'])).
% 0.20/0.52  thf('117', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('119', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.52          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.52      inference('demod', [status(thm)], ['116', '117', '118'])).
% 0.20/0.52  thf('120', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.52          | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.20/0.52      inference('clc', [status(thm)], ['113', '119'])).
% 0.20/0.52  thf('121', plain,
% 0.20/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.52        | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['74', '120'])).
% 0.20/0.53  thf('122', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i]:
% 0.20/0.53         ((r2_hidden @ X1 @ X2) | ~ (r1_tarski @ (k1_tarski @ X1) @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.53  thf('123', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['121', '122'])).
% 0.20/0.53  thf('124', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('125', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.20/0.53          | ~ (r2_hidden @ X14 @ (k1_tops_1 @ X15 @ X16))
% 0.20/0.53          | (m1_connsp_2 @ X16 @ X15 @ X14)
% 0.20/0.53          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.20/0.53          | ~ (l1_pre_topc @ X15)
% 0.20/0.53          | ~ (v2_pre_topc @ X15)
% 0.20/0.53          | (v2_struct_0 @ X15))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.20/0.53  thf('126', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_A)
% 0.20/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.20/0.53          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['124', '125'])).
% 0.20/0.53  thf('127', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('128', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('129', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((v2_struct_0 @ sk_A)
% 0.20/0.53          | (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.20/0.53          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['126', '127', '128'])).
% 0.20/0.53  thf('130', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.20/0.53        | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['123', '129'])).
% 0.20/0.53  thf('131', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('132', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.20/0.53        | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['130', '131'])).
% 0.20/0.53  thf('133', plain,
% 0.20/0.53      ((~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.20/0.53         <= (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('split', [status(esa)], ['8'])).
% 0.20/0.53  thf('134', plain, (~ ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['9', '71'])).
% 0.20/0.53  thf('135', plain, (~ (m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['133', '134'])).
% 0.20/0.53  thf('136', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('clc', [status(thm)], ['132', '135'])).
% 0.20/0.53  thf('137', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('138', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('clc', [status(thm)], ['136', '137'])).
% 0.20/0.53  thf('139', plain,
% 0.20/0.53      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup+', [status(thm)], ['1', '138'])).
% 0.20/0.53  thf('140', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.53      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.53  thf('141', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['139', '140'])).
% 0.20/0.53  thf('142', plain,
% 0.20/0.53      (![X11 : $i]:
% 0.20/0.53         (~ (v1_xboole_0 @ (k2_struct_0 @ X11))
% 0.20/0.53          | ~ (l1_struct_0 @ X11)
% 0.20/0.53          | (v2_struct_0 @ X11))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.20/0.53  thf('143', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['141', '142'])).
% 0.20/0.53  thf('144', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.53      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.53  thf('145', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('demod', [status(thm)], ['143', '144'])).
% 0.20/0.53  thf('146', plain, ($false), inference('demod', [status(thm)], ['0', '145'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
