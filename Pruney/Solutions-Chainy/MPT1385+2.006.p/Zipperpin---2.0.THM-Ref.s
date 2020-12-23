%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UnCWzSgXBH

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:59 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 327 expanded)
%              Number of leaves         :   29 ( 102 expanded)
%              Depth                    :   28
%              Number of atoms          : 1027 (4430 expanded)
%              Number of equality atoms :   12 (  43 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X8 != X7 )
      | ( r2_hidden @ X8 @ X9 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X7: $i] :
      ( r2_hidden @ X7 @ ( k1_tarski @ X7 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( X10 = X7 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('9',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

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

thf('17',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m2_connsp_2 @ X29 @ X28 @ X27 )
      | ( r1_tarski @ X27 @ ( k1_tops_1 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ~ ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('24',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ X22 )
      | ( ( k6_domain_1 @ X22 @ X23 )
        = ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('25',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1 )
    | ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
   <= ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ( ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['25','27'])).

thf('29',plain,
    ( ~ ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1 )
    | ~ ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1 )
    | ~ ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1 )
   <= ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['26'])).

thf('32',plain,(
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

thf('33',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_connsp_2 @ X26 @ X25 @ X24 )
      | ( r2_hidden @ X24 @ ( k1_tops_1 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_2 ) )
      | ~ ( m1_connsp_2 @ sk_C_2 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_2 ) )
      | ~ ( m1_connsp_2 @ sk_C_2 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C_2 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C_2 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C_2 ) )
   <= ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('44',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_C_2 ) )
   <= ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('46',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( r1_tarski @ X27 @ ( k1_tops_1 @ X28 @ X29 ) )
      | ( m2_connsp_2 @ X29 @ X28 @ X27 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('55',plain,
    ( ~ ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
   <= ~ ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['29'])).

thf('56',plain,
    ( ( ~ ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      & ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      & ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('59',plain,(
    ! [X21: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('60',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      & ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('62',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('63',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      & ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ~ ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['26'])).

thf('68',plain,(
    m2_connsp_2 @ sk_C_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['30','66','67'])).

thf('69',plain,
    ( ( m2_connsp_2 @ sk_C_2 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['28','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['22','69'])).

thf('71',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ~ ( r2_hidden @ X24 @ ( k1_tops_1 @ X25 @ X26 ) )
      | ( m1_connsp_2 @ X26 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C_2 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C_2 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_2 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['73','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1 )
   <= ~ ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['29'])).

thf('84',plain,(
    ~ ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['30','66'])).

thf('85',plain,(
    ~ ( m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['82','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X21: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['61','62'])).

thf('92',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    $false ),
    inference(demod,[status(thm)],['0','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UnCWzSgXBH
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:20:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.59/0.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.79  % Solved by: fo/fo7.sh
% 0.59/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.79  % done 441 iterations in 0.303s
% 0.59/0.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.79  % SZS output start Refutation
% 0.59/0.79  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.59/0.79  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.59/0.79  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.59/0.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.79  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.59/0.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.79  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.59/0.79  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.79  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.59/0.79  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.59/0.79  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.59/0.79  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.79  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.59/0.79  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.59/0.79  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.59/0.79  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.79  thf(t10_connsp_2, conjecture,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.79       ( ![B:$i]:
% 0.59/0.79         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.79           ( ![C:$i]:
% 0.59/0.79             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.79               ( ( m2_connsp_2 @
% 0.59/0.79                   C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.59/0.79                 ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ))).
% 0.59/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.79    (~( ![A:$i]:
% 0.59/0.79        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.59/0.79            ( l1_pre_topc @ A ) ) =>
% 0.59/0.79          ( ![B:$i]:
% 0.59/0.79            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.79              ( ![C:$i]:
% 0.59/0.79                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.79                  ( ( m2_connsp_2 @
% 0.59/0.79                      C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.59/0.79                    ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ) )),
% 0.59/0.79    inference('cnf.neg', [status(esa)], [t10_connsp_2])).
% 0.59/0.79  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(d1_tarski, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.59/0.79       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.59/0.79  thf('1', plain,
% 0.59/0.79      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.59/0.79         (((X8) != (X7)) | (r2_hidden @ X8 @ X9) | ((X9) != (k1_tarski @ X7)))),
% 0.59/0.79      inference('cnf', [status(esa)], [d1_tarski])).
% 0.59/0.79  thf('2', plain, (![X7 : $i]: (r2_hidden @ X7 @ (k1_tarski @ X7))),
% 0.59/0.79      inference('simplify', [status(thm)], ['1'])).
% 0.59/0.79  thf('3', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('4', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(d2_subset_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( ( v1_xboole_0 @ A ) =>
% 0.59/0.79         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.59/0.79       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.59/0.79         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.59/0.79  thf('5', plain,
% 0.59/0.79      (![X12 : $i, X13 : $i]:
% 0.59/0.79         (~ (m1_subset_1 @ X12 @ X13)
% 0.59/0.79          | (r2_hidden @ X12 @ X13)
% 0.59/0.79          | (v1_xboole_0 @ X13))),
% 0.59/0.79      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.59/0.79  thf('6', plain,
% 0.59/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79        | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['4', '5'])).
% 0.59/0.79  thf(d3_tarski, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( r1_tarski @ A @ B ) <=>
% 0.59/0.79       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.59/0.79  thf('7', plain,
% 0.59/0.79      (![X4 : $i, X6 : $i]:
% 0.59/0.79         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.59/0.79      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.79  thf('8', plain,
% 0.59/0.79      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.59/0.79         (~ (r2_hidden @ X10 @ X9)
% 0.59/0.79          | ((X10) = (X7))
% 0.59/0.79          | ((X9) != (k1_tarski @ X7)))),
% 0.59/0.79      inference('cnf', [status(esa)], [d1_tarski])).
% 0.59/0.79  thf('9', plain,
% 0.59/0.79      (![X7 : $i, X10 : $i]:
% 0.59/0.79         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 0.59/0.79      inference('simplify', [status(thm)], ['8'])).
% 0.59/0.79  thf('10', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.59/0.79          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['7', '9'])).
% 0.59/0.79  thf('11', plain,
% 0.59/0.79      (![X4 : $i, X6 : $i]:
% 0.59/0.79         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.59/0.79      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.79  thf('12', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (~ (r2_hidden @ X0 @ X1)
% 0.59/0.79          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.59/0.79          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.59/0.79      inference('sup-', [status(thm)], ['10', '11'])).
% 0.59/0.79  thf('13', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.59/0.79      inference('simplify', [status(thm)], ['12'])).
% 0.59/0.79  thf('14', plain,
% 0.59/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79        | (r1_tarski @ (k1_tarski @ sk_B_1) @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['6', '13'])).
% 0.59/0.79  thf(t3_subset, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.59/0.79  thf('15', plain,
% 0.59/0.79      (![X17 : $i, X19 : $i]:
% 0.59/0.79         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 0.59/0.79      inference('cnf', [status(esa)], [t3_subset])).
% 0.59/0.79  thf('16', plain,
% 0.59/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.59/0.79           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['14', '15'])).
% 0.59/0.79  thf(d2_connsp_2, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.79       ( ![B:$i]:
% 0.59/0.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.79           ( ![C:$i]:
% 0.59/0.79             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.79               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.59/0.79                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.59/0.79  thf('17', plain,
% 0.59/0.79      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.59/0.79         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.59/0.79          | ~ (m2_connsp_2 @ X29 @ X28 @ X27)
% 0.59/0.79          | (r1_tarski @ X27 @ (k1_tops_1 @ X28 @ X29))
% 0.59/0.79          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.59/0.79          | ~ (l1_pre_topc @ X28)
% 0.59/0.79          | ~ (v2_pre_topc @ X28))),
% 0.59/0.79      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.59/0.79  thf('18', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79          | ~ (v2_pre_topc @ sk_A)
% 0.59/0.79          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.79          | (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ X0))
% 0.59/0.79          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.79  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('21', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.79          | (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ X0))
% 0.59/0.79          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.59/0.79      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.59/0.79  thf('22', plain,
% 0.59/0.79      ((~ (m2_connsp_2 @ sk_C_2 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.59/0.79        | (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_C_2))
% 0.59/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['3', '21'])).
% 0.59/0.79  thf('23', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(redefinition_k6_domain_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.59/0.79       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.59/0.79  thf('24', plain,
% 0.59/0.79      (![X22 : $i, X23 : $i]:
% 0.59/0.79         ((v1_xboole_0 @ X22)
% 0.59/0.79          | ~ (m1_subset_1 @ X23 @ X22)
% 0.59/0.79          | ((k6_domain_1 @ X22 @ X23) = (k1_tarski @ X23)))),
% 0.59/0.79      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.59/0.79  thf('25', plain,
% 0.59/0.79      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.59/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['23', '24'])).
% 0.59/0.79  thf('26', plain,
% 0.59/0.79      (((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1)
% 0.59/0.79        | (m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.59/0.79           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('27', plain,
% 0.59/0.79      (((m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.59/0.79         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.59/0.79         <= (((m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.59/0.79               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.59/0.79      inference('split', [status(esa)], ['26'])).
% 0.59/0.79  thf('28', plain,
% 0.59/0.79      ((((m2_connsp_2 @ sk_C_2 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.59/0.79         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.79         <= (((m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.59/0.79               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.59/0.79      inference('sup+', [status(thm)], ['25', '27'])).
% 0.59/0.79  thf('29', plain,
% 0.59/0.79      ((~ (m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1)
% 0.59/0.79        | ~ (m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.59/0.79             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('30', plain,
% 0.59/0.79      (~ ((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1)) | 
% 0.59/0.79       ~
% 0.59/0.79       ((m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.59/0.79         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.59/0.79      inference('split', [status(esa)], ['29'])).
% 0.59/0.79  thf('31', plain,
% 0.59/0.79      (((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1))
% 0.59/0.79         <= (((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1)))),
% 0.59/0.79      inference('split', [status(esa)], ['26'])).
% 0.59/0.79  thf('32', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(d1_connsp_2, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.79       ( ![B:$i]:
% 0.59/0.79         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.79           ( ![C:$i]:
% 0.59/0.79             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.79               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.59/0.79                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.59/0.79  thf('33', plain,
% 0.59/0.79      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.59/0.79         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.59/0.79          | ~ (m1_connsp_2 @ X26 @ X25 @ X24)
% 0.59/0.79          | (r2_hidden @ X24 @ (k1_tops_1 @ X25 @ X26))
% 0.59/0.79          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.59/0.79          | ~ (l1_pre_topc @ X25)
% 0.59/0.79          | ~ (v2_pre_topc @ X25)
% 0.59/0.79          | (v2_struct_0 @ X25))),
% 0.59/0.79      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.59/0.79  thf('34', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((v2_struct_0 @ sk_A)
% 0.59/0.79          | ~ (v2_pre_topc @ sk_A)
% 0.59/0.79          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.79          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_2))
% 0.59/0.79          | ~ (m1_connsp_2 @ sk_C_2 @ sk_A @ X0)
% 0.59/0.79          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['32', '33'])).
% 0.59/0.79  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('37', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((v2_struct_0 @ sk_A)
% 0.59/0.79          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_2))
% 0.59/0.79          | ~ (m1_connsp_2 @ sk_C_2 @ sk_A @ X0)
% 0.59/0.79          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.59/0.79  thf('38', plain,
% 0.59/0.79      (((~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.59/0.79         | (r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C_2))
% 0.59/0.79         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['31', '37'])).
% 0.59/0.79  thf('39', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('40', plain,
% 0.59/0.79      ((((r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C_2))
% 0.59/0.79         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1)))),
% 0.59/0.79      inference('demod', [status(thm)], ['38', '39'])).
% 0.59/0.79  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('42', plain,
% 0.59/0.79      (((r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C_2)))
% 0.59/0.79         <= (((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1)))),
% 0.59/0.79      inference('clc', [status(thm)], ['40', '41'])).
% 0.59/0.79  thf('43', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.59/0.79      inference('simplify', [status(thm)], ['12'])).
% 0.59/0.79  thf('44', plain,
% 0.59/0.79      (((r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_C_2)))
% 0.59/0.79         <= (((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['42', '43'])).
% 0.59/0.79  thf('45', plain,
% 0.59/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.59/0.79           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['14', '15'])).
% 0.59/0.79  thf('46', plain,
% 0.59/0.79      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.59/0.79         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.59/0.79          | ~ (r1_tarski @ X27 @ (k1_tops_1 @ X28 @ X29))
% 0.59/0.79          | (m2_connsp_2 @ X29 @ X28 @ X27)
% 0.59/0.79          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.59/0.79          | ~ (l1_pre_topc @ X28)
% 0.59/0.79          | ~ (v2_pre_topc @ X28))),
% 0.59/0.79      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.59/0.79  thf('47', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79          | ~ (v2_pre_topc @ sk_A)
% 0.59/0.79          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.79          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.59/0.79          | ~ (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['45', '46'])).
% 0.59/0.79  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('50', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.79          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.59/0.79          | ~ (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.59/0.79      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.59/0.79  thf('51', plain,
% 0.59/0.79      ((((m2_connsp_2 @ sk_C_2 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.59/0.79         | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.79         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.79         <= (((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['44', '50'])).
% 0.59/0.79  thf('52', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('53', plain,
% 0.59/0.79      ((((m2_connsp_2 @ sk_C_2 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.59/0.79         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.79         <= (((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1)))),
% 0.59/0.79      inference('demod', [status(thm)], ['51', '52'])).
% 0.59/0.79  thf('54', plain,
% 0.59/0.79      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.59/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['23', '24'])).
% 0.59/0.79  thf('55', plain,
% 0.59/0.79      ((~ (m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.59/0.79           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.59/0.79         <= (~
% 0.59/0.79             ((m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.59/0.79               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.59/0.79      inference('split', [status(esa)], ['29'])).
% 0.59/0.79  thf('56', plain,
% 0.59/0.79      (((~ (m2_connsp_2 @ sk_C_2 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.59/0.79         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.79         <= (~
% 0.59/0.79             ((m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.59/0.79               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['54', '55'])).
% 0.59/0.79  thf('57', plain,
% 0.59/0.79      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.79         <= (~
% 0.59/0.79             ((m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.59/0.79               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) & 
% 0.59/0.79             ((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['53', '56'])).
% 0.59/0.79  thf('58', plain,
% 0.59/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.59/0.79         <= (~
% 0.59/0.79             ((m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.59/0.79               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) & 
% 0.59/0.79             ((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1)))),
% 0.59/0.79      inference('simplify', [status(thm)], ['57'])).
% 0.59/0.79  thf(fc2_struct_0, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.59/0.79       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.59/0.79  thf('59', plain,
% 0.59/0.79      (![X21 : $i]:
% 0.59/0.79         (~ (v1_xboole_0 @ (u1_struct_0 @ X21))
% 0.59/0.79          | ~ (l1_struct_0 @ X21)
% 0.59/0.79          | (v2_struct_0 @ X21))),
% 0.59/0.79      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.59/0.79  thf('60', plain,
% 0.59/0.79      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.59/0.79         <= (~
% 0.59/0.79             ((m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.59/0.79               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) & 
% 0.59/0.79             ((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['58', '59'])).
% 0.59/0.79  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(dt_l1_pre_topc, axiom,
% 0.59/0.79    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.59/0.79  thf('62', plain,
% 0.59/0.79      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.59/0.79      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.59/0.79  thf('63', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.79      inference('sup-', [status(thm)], ['61', '62'])).
% 0.59/0.79  thf('64', plain,
% 0.59/0.79      (((v2_struct_0 @ sk_A))
% 0.59/0.79         <= (~
% 0.59/0.79             ((m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.59/0.79               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) & 
% 0.59/0.79             ((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1)))),
% 0.59/0.79      inference('demod', [status(thm)], ['60', '63'])).
% 0.59/0.79  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('66', plain,
% 0.59/0.79      (((m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.59/0.79         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) | 
% 0.59/0.79       ~ ((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1))),
% 0.59/0.79      inference('sup-', [status(thm)], ['64', '65'])).
% 0.59/0.79  thf('67', plain,
% 0.59/0.79      (((m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.59/0.79         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) | 
% 0.59/0.79       ((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1))),
% 0.59/0.79      inference('split', [status(esa)], ['26'])).
% 0.59/0.79  thf('68', plain,
% 0.59/0.79      (((m2_connsp_2 @ sk_C_2 @ sk_A @ 
% 0.59/0.79         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.59/0.79      inference('sat_resolution*', [status(thm)], ['30', '66', '67'])).
% 0.59/0.79  thf('69', plain,
% 0.59/0.79      (((m2_connsp_2 @ sk_C_2 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.59/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('simpl_trail', [status(thm)], ['28', '68'])).
% 0.59/0.79  thf('70', plain,
% 0.59/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79        | (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_C_2)))),
% 0.59/0.79      inference('clc', [status(thm)], ['22', '69'])).
% 0.59/0.79  thf('71', plain,
% 0.59/0.79      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.59/0.79         (~ (r2_hidden @ X3 @ X4)
% 0.59/0.79          | (r2_hidden @ X3 @ X5)
% 0.59/0.79          | ~ (r1_tarski @ X4 @ X5))),
% 0.59/0.79      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.79  thf('72', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_2))
% 0.59/0.79          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B_1)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['70', '71'])).
% 0.59/0.79  thf('73', plain,
% 0.59/0.79      (((r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C_2))
% 0.59/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['2', '72'])).
% 0.59/0.79  thf('74', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('75', plain,
% 0.59/0.79      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.59/0.79         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.59/0.79          | ~ (r2_hidden @ X24 @ (k1_tops_1 @ X25 @ X26))
% 0.59/0.79          | (m1_connsp_2 @ X26 @ X25 @ X24)
% 0.59/0.79          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.59/0.79          | ~ (l1_pre_topc @ X25)
% 0.59/0.79          | ~ (v2_pre_topc @ X25)
% 0.59/0.79          | (v2_struct_0 @ X25))),
% 0.59/0.79      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.59/0.79  thf('76', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((v2_struct_0 @ sk_A)
% 0.59/0.79          | ~ (v2_pre_topc @ sk_A)
% 0.59/0.79          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.79          | (m1_connsp_2 @ sk_C_2 @ sk_A @ X0)
% 0.59/0.79          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_2))
% 0.59/0.79          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['74', '75'])).
% 0.59/0.79  thf('77', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('79', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((v2_struct_0 @ sk_A)
% 0.59/0.79          | (m1_connsp_2 @ sk_C_2 @ sk_A @ X0)
% 0.59/0.79          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_2))
% 0.59/0.79          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.59/0.79  thf('80', plain,
% 0.59/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.59/0.79        | (m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1)
% 0.59/0.79        | (v2_struct_0 @ sk_A))),
% 0.59/0.79      inference('sup-', [status(thm)], ['73', '79'])).
% 0.59/0.79  thf('81', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('82', plain,
% 0.59/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79        | (m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1)
% 0.59/0.79        | (v2_struct_0 @ sk_A))),
% 0.59/0.79      inference('demod', [status(thm)], ['80', '81'])).
% 0.59/0.79  thf('83', plain,
% 0.59/0.79      ((~ (m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1))
% 0.59/0.79         <= (~ ((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1)))),
% 0.59/0.79      inference('split', [status(esa)], ['29'])).
% 0.59/0.79  thf('84', plain, (~ ((m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1))),
% 0.59/0.79      inference('sat_resolution*', [status(thm)], ['30', '66'])).
% 0.59/0.79  thf('85', plain, (~ (m1_connsp_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 0.59/0.79      inference('simpl_trail', [status(thm)], ['83', '84'])).
% 0.59/0.79  thf('86', plain,
% 0.59/0.79      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('clc', [status(thm)], ['82', '85'])).
% 0.59/0.79  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('88', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.59/0.79      inference('clc', [status(thm)], ['86', '87'])).
% 0.59/0.79  thf('89', plain,
% 0.59/0.79      (![X21 : $i]:
% 0.59/0.79         (~ (v1_xboole_0 @ (u1_struct_0 @ X21))
% 0.59/0.79          | ~ (l1_struct_0 @ X21)
% 0.59/0.79          | (v2_struct_0 @ X21))),
% 0.59/0.79      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.59/0.79  thf('90', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.59/0.79      inference('sup-', [status(thm)], ['88', '89'])).
% 0.59/0.79  thf('91', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.79      inference('sup-', [status(thm)], ['61', '62'])).
% 0.59/0.79  thf('92', plain, ((v2_struct_0 @ sk_A)),
% 0.59/0.79      inference('demod', [status(thm)], ['90', '91'])).
% 0.59/0.79  thf('93', plain, ($false), inference('demod', [status(thm)], ['0', '92'])).
% 0.59/0.79  
% 0.59/0.79  % SZS output end Refutation
% 0.59/0.79  
% 0.59/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
