%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.23EVP4Pt8L

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:01 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 249 expanded)
%              Number of leaves         :   29 (  82 expanded)
%              Depth                    :   22
%              Number of atoms          : 1126 (3526 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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

thf('0',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

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
    ! [X39: $i,X40: $i] :
      ( ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ X39 )
      | ( ( k6_domain_1 @ X39 @ X40 )
        = ( k1_tarski @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('4',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r2_hidden @ X32 @ X33 )
      | ( v1_xboole_0 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X28 @ X30 ) @ X31 )
      | ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( r2_hidden @ X28 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k2_tarski @ sk_B @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('17',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X34: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

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

thf('21',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( m2_connsp_2 @ X46 @ X45 @ X44 )
      | ( r1_tarski @ X44 @ ( k1_tops_1 @ X45 @ X46 ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','25'])).

thf('27',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','26'])).

thf('28',plain,
    ( ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('30',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ X28 @ X29 )
      | ~ ( r1_tarski @ ( k2_tarski @ X28 @ X30 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('34',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X42 ) )
      | ~ ( r2_hidden @ X41 @ ( k1_tops_1 @ X42 @ X43 ) )
      | ( m1_connsp_2 @ X43 @ X42 @ X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('46',plain,(
    ! [X38: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X38 ) )
      | ~ ( l1_struct_0 @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('47',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('49',plain,(
    ! [X37: $i] :
      ( ( l1_struct_0 @ X37 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('50',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('55',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X42 ) )
      | ~ ( m1_connsp_2 @ X43 @ X42 @ X41 )
      | ( r2_hidden @ X41 @ ( k1_tops_1 @ X42 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('68',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X28 @ X30 ) @ X31 )
      | ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( r2_hidden @ X28 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
        | ( r1_tarski @ ( k2_tarski @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_B @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('72',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('74',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( r1_tarski @ X44 @ ( k1_tops_1 @ X45 @ X46 ) )
      | ( m2_connsp_2 @ X46 @ X45 @ X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['72','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('83',plain,
    ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,
    ( ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X38: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X38 ) )
      | ~ ( l1_struct_0 @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('88',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','53','54','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.23EVP4Pt8L
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:47:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.53  % Solved by: fo/fo7.sh
% 0.35/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.53  % done 136 iterations in 0.067s
% 0.35/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.53  % SZS output start Refutation
% 0.35/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.35/0.53  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.35/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.53  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.35/0.53  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.35/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.35/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.35/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.53  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.35/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.53  thf(t10_connsp_2, conjecture,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.53           ( ![C:$i]:
% 0.35/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53               ( ( m2_connsp_2 @
% 0.35/0.53                   C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.35/0.53                 ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ))).
% 0.35/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.53    (~( ![A:$i]:
% 0.35/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.35/0.53            ( l1_pre_topc @ A ) ) =>
% 0.35/0.53          ( ![B:$i]:
% 0.35/0.53            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.53              ( ![C:$i]:
% 0.35/0.53                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53                  ( ( m2_connsp_2 @
% 0.35/0.53                      C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.35/0.53                    ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ) )),
% 0.35/0.53    inference('cnf.neg', [status(esa)], [t10_connsp_2])).
% 0.35/0.53  thf('0', plain,
% 0.35/0.53      ((~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.35/0.53        | ~ (m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('1', plain,
% 0.35/0.53      (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.35/0.53       ~
% 0.35/0.53       ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.35/0.53      inference('split', [status(esa)], ['0'])).
% 0.35/0.53  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(redefinition_k6_domain_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.35/0.53       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.35/0.53  thf('3', plain,
% 0.35/0.53      (![X39 : $i, X40 : $i]:
% 0.35/0.53         ((v1_xboole_0 @ X39)
% 0.35/0.53          | ~ (m1_subset_1 @ X40 @ X39)
% 0.35/0.53          | ((k6_domain_1 @ X39 @ X40) = (k1_tarski @ X40)))),
% 0.35/0.53      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.35/0.53  thf('4', plain,
% 0.35/0.53      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.35/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.35/0.53  thf('5', plain,
% 0.35/0.53      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.35/0.53        | (m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('6', plain,
% 0.35/0.53      (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.35/0.53         <= (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.53      inference('split', [status(esa)], ['5'])).
% 0.35/0.53  thf('7', plain,
% 0.35/0.53      ((((m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.35/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.35/0.53         <= (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.53      inference('sup+', [status(thm)], ['4', '6'])).
% 0.35/0.53  thf('8', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('9', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(t2_subset, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ A @ B ) =>
% 0.35/0.53       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.35/0.53  thf('10', plain,
% 0.35/0.53      (![X32 : $i, X33 : $i]:
% 0.35/0.53         ((r2_hidden @ X32 @ X33)
% 0.35/0.53          | (v1_xboole_0 @ X33)
% 0.35/0.53          | ~ (m1_subset_1 @ X32 @ X33))),
% 0.35/0.53      inference('cnf', [status(esa)], [t2_subset])).
% 0.35/0.53  thf('11', plain,
% 0.35/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.35/0.53  thf('12', plain,
% 0.35/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.35/0.53  thf(t38_zfmisc_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.35/0.53       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.35/0.53  thf('13', plain,
% 0.35/0.53      (![X28 : $i, X30 : $i, X31 : $i]:
% 0.35/0.53         ((r1_tarski @ (k2_tarski @ X28 @ X30) @ X31)
% 0.35/0.53          | ~ (r2_hidden @ X30 @ X31)
% 0.35/0.53          | ~ (r2_hidden @ X28 @ X31))),
% 0.35/0.53      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.35/0.53  thf('14', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53          | (r1_tarski @ (k2_tarski @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.53  thf('15', plain,
% 0.35/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53        | (r1_tarski @ (k2_tarski @ sk_B @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.35/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['11', '14'])).
% 0.35/0.53  thf(t69_enumset1, axiom,
% 0.35/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.35/0.53  thf('16', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.53  thf('17', plain,
% 0.35/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53        | (r1_tarski @ (k1_tarski @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.35/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('demod', [status(thm)], ['15', '16'])).
% 0.35/0.53  thf('18', plain,
% 0.35/0.53      (((r1_tarski @ (k1_tarski @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.35/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('simplify', [status(thm)], ['17'])).
% 0.35/0.53  thf(t3_subset, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.35/0.53  thf('19', plain,
% 0.35/0.53      (![X34 : $i, X36 : $i]:
% 0.35/0.53         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X34 @ X36))),
% 0.35/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.35/0.53  thf('20', plain,
% 0.35/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.35/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.35/0.53  thf(d2_connsp_2, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53           ( ![C:$i]:
% 0.35/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.35/0.53                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.35/0.53  thf('21', plain,
% 0.35/0.53      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.35/0.53          | ~ (m2_connsp_2 @ X46 @ X45 @ X44)
% 0.35/0.53          | (r1_tarski @ X44 @ (k1_tops_1 @ X45 @ X46))
% 0.35/0.53          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.35/0.53          | ~ (l1_pre_topc @ X45)
% 0.35/0.53          | ~ (v2_pre_topc @ X45))),
% 0.35/0.53      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.35/0.53  thf('22', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.35/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.35/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.53          | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.35/0.53          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.35/0.53  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('25', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.53          | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.35/0.53          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.35/0.53      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.35/0.53  thf('26', plain,
% 0.35/0.53      ((~ (m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.35/0.53        | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['8', '25'])).
% 0.35/0.53  thf('27', plain,
% 0.35/0.53      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53         | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.35/0.53         <= (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['7', '26'])).
% 0.35/0.53  thf('28', plain,
% 0.35/0.53      ((((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.35/0.53         <= (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.53      inference('simplify', [status(thm)], ['27'])).
% 0.35/0.53  thf('29', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.53  thf('30', plain,
% 0.35/0.53      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.35/0.53         ((r2_hidden @ X28 @ X29)
% 0.35/0.53          | ~ (r1_tarski @ (k2_tarski @ X28 @ X30) @ X29))),
% 0.35/0.53      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.35/0.53  thf('31', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.35/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.35/0.53  thf('32', plain,
% 0.35/0.53      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.35/0.53         <= (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['28', '31'])).
% 0.35/0.53  thf('33', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(d1_connsp_2, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.53           ( ![C:$i]:
% 0.35/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.53               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.35/0.53                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.35/0.53  thf('34', plain,
% 0.35/0.53      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X42))
% 0.35/0.53          | ~ (r2_hidden @ X41 @ (k1_tops_1 @ X42 @ X43))
% 0.35/0.53          | (m1_connsp_2 @ X43 @ X42 @ X41)
% 0.35/0.53          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.35/0.53          | ~ (l1_pre_topc @ X42)
% 0.35/0.53          | ~ (v2_pre_topc @ X42)
% 0.35/0.53          | (v2_struct_0 @ X42))),
% 0.35/0.53      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.35/0.53  thf('35', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((v2_struct_0 @ sk_A)
% 0.35/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.35/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.35/0.53          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.35/0.53          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.35/0.53  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('38', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((v2_struct_0 @ sk_A)
% 0.35/0.53          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.35/0.53          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.35/0.53  thf('39', plain,
% 0.35/0.53      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.35/0.53         | (m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.35/0.53         | (v2_struct_0 @ sk_A)))
% 0.35/0.53         <= (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['32', '38'])).
% 0.35/0.53  thf('40', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('41', plain,
% 0.35/0.53      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53         | (m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.35/0.53         | (v2_struct_0 @ sk_A)))
% 0.35/0.53         <= (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.53      inference('demod', [status(thm)], ['39', '40'])).
% 0.35/0.53  thf('42', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('43', plain,
% 0.35/0.53      ((((m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.35/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.35/0.53         <= (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.53      inference('clc', [status(thm)], ['41', '42'])).
% 0.35/0.53  thf('44', plain,
% 0.35/0.53      ((~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 0.35/0.53         <= (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.53      inference('split', [status(esa)], ['0'])).
% 0.35/0.53  thf('45', plain,
% 0.35/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.35/0.53         <= (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) & 
% 0.35/0.53             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.35/0.53  thf(fc2_struct_0, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.35/0.53       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.35/0.53  thf('46', plain,
% 0.35/0.53      (![X38 : $i]:
% 0.35/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X38))
% 0.35/0.53          | ~ (l1_struct_0 @ X38)
% 0.35/0.53          | (v2_struct_0 @ X38))),
% 0.35/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.35/0.53  thf('47', plain,
% 0.35/0.53      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.35/0.53         <= (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) & 
% 0.35/0.53             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['45', '46'])).
% 0.35/0.53  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(dt_l1_pre_topc, axiom,
% 0.35/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.35/0.53  thf('49', plain,
% 0.35/0.53      (![X37 : $i]: ((l1_struct_0 @ X37) | ~ (l1_pre_topc @ X37))),
% 0.35/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.53  thf('50', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.53      inference('sup-', [status(thm)], ['48', '49'])).
% 0.35/0.53  thf('51', plain,
% 0.35/0.53      (((v2_struct_0 @ sk_A))
% 0.35/0.53         <= (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) & 
% 0.35/0.53             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.53      inference('demod', [status(thm)], ['47', '50'])).
% 0.35/0.53  thf('52', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('53', plain,
% 0.35/0.53      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.35/0.53       ~
% 0.35/0.53       ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['51', '52'])).
% 0.35/0.53  thf('54', plain,
% 0.35/0.53      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.35/0.53       ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.35/0.53      inference('split', [status(esa)], ['5'])).
% 0.35/0.53  thf('55', plain,
% 0.35/0.53      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 0.35/0.53         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.53      inference('split', [status(esa)], ['5'])).
% 0.35/0.53  thf('56', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('57', plain,
% 0.35/0.53      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X42))
% 0.35/0.53          | ~ (m1_connsp_2 @ X43 @ X42 @ X41)
% 0.35/0.53          | (r2_hidden @ X41 @ (k1_tops_1 @ X42 @ X43))
% 0.35/0.53          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.35/0.53          | ~ (l1_pre_topc @ X42)
% 0.35/0.53          | ~ (v2_pre_topc @ X42)
% 0.35/0.53          | (v2_struct_0 @ X42))),
% 0.35/0.53      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.35/0.53  thf('58', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((v2_struct_0 @ sk_A)
% 0.35/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.35/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.35/0.53          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.53          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.35/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['56', '57'])).
% 0.35/0.53  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('61', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((v2_struct_0 @ sk_A)
% 0.35/0.53          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.53          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.35/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.35/0.53  thf('62', plain,
% 0.35/0.53      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.35/0.53         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.53         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['55', '61'])).
% 0.35/0.53  thf('63', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('64', plain,
% 0.35/0.53      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A)))
% 0.35/0.53         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.53      inference('demod', [status(thm)], ['62', '63'])).
% 0.35/0.53  thf('65', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('66', plain,
% 0.35/0.53      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.35/0.53         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.53      inference('clc', [status(thm)], ['64', '65'])).
% 0.35/0.53  thf('67', plain,
% 0.35/0.53      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.35/0.53         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.53      inference('clc', [status(thm)], ['64', '65'])).
% 0.35/0.53  thf('68', plain,
% 0.35/0.53      (![X28 : $i, X30 : $i, X31 : $i]:
% 0.35/0.53         ((r1_tarski @ (k2_tarski @ X28 @ X30) @ X31)
% 0.35/0.53          | ~ (r2_hidden @ X30 @ X31)
% 0.35/0.53          | ~ (r2_hidden @ X28 @ X31))),
% 0.35/0.53      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.35/0.53  thf('69', plain,
% 0.35/0.53      ((![X0 : $i]:
% 0.35/0.53          (~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.53           | (r1_tarski @ (k2_tarski @ X0 @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.35/0.53         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['67', '68'])).
% 0.35/0.53  thf('70', plain,
% 0.35/0.53      (((r1_tarski @ (k2_tarski @ sk_B @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.35/0.53         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['66', '69'])).
% 0.35/0.53  thf('71', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.35/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.53  thf('72', plain,
% 0.35/0.53      (((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.35/0.53         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.53      inference('demod', [status(thm)], ['70', '71'])).
% 0.35/0.53  thf('73', plain,
% 0.35/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.35/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.35/0.53  thf('74', plain,
% 0.35/0.53      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.35/0.53         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.35/0.53          | ~ (r1_tarski @ X44 @ (k1_tops_1 @ X45 @ X46))
% 0.35/0.53          | (m2_connsp_2 @ X46 @ X45 @ X44)
% 0.35/0.53          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.35/0.53          | ~ (l1_pre_topc @ X45)
% 0.35/0.53          | ~ (v2_pre_topc @ X45))),
% 0.35/0.53      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.35/0.53  thf('75', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.35/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.35/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.53          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.35/0.53          | ~ (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['73', '74'])).
% 0.35/0.53  thf('76', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('78', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.53          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.35/0.53          | ~ (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.35/0.53      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.35/0.53  thf('79', plain,
% 0.35/0.53      ((((m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.35/0.53         | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.35/0.53         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['72', '78'])).
% 0.35/0.53  thf('80', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('81', plain,
% 0.35/0.53      ((((m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.35/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.35/0.53         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.53      inference('demod', [status(thm)], ['79', '80'])).
% 0.35/0.53  thf('82', plain,
% 0.35/0.53      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.35/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.35/0.53  thf('83', plain,
% 0.35/0.53      ((~ (m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.35/0.53         <= (~
% 0.35/0.53             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.53      inference('split', [status(esa)], ['0'])).
% 0.35/0.53  thf('84', plain,
% 0.35/0.53      (((~ (m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.35/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.35/0.53         <= (~
% 0.35/0.53             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['82', '83'])).
% 0.35/0.53  thf('85', plain,
% 0.35/0.53      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.35/0.53         <= (~
% 0.35/0.53             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.35/0.53             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['81', '84'])).
% 0.35/0.53  thf('86', plain,
% 0.35/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.35/0.53         <= (~
% 0.35/0.53             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.35/0.53             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.53      inference('simplify', [status(thm)], ['85'])).
% 0.35/0.53  thf('87', plain,
% 0.35/0.53      (![X38 : $i]:
% 0.35/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X38))
% 0.35/0.53          | ~ (l1_struct_0 @ X38)
% 0.35/0.53          | (v2_struct_0 @ X38))),
% 0.35/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.35/0.53  thf('88', plain,
% 0.35/0.53      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.35/0.53         <= (~
% 0.35/0.53             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.35/0.53             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['86', '87'])).
% 0.35/0.53  thf('89', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.53      inference('sup-', [status(thm)], ['48', '49'])).
% 0.35/0.53  thf('90', plain,
% 0.35/0.53      (((v2_struct_0 @ sk_A))
% 0.35/0.53         <= (~
% 0.35/0.53             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.35/0.53             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.53      inference('demod', [status(thm)], ['88', '89'])).
% 0.35/0.53  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('92', plain,
% 0.35/0.53      (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.35/0.53       ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['90', '91'])).
% 0.35/0.53  thf('93', plain, ($false),
% 0.35/0.53      inference('sat_resolution*', [status(thm)], ['1', '53', '54', '92'])).
% 0.35/0.53  
% 0.35/0.53  % SZS output end Refutation
% 0.35/0.53  
% 0.35/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
