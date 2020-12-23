%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fD7ZHQbp2Q

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:59 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :  192 (1808 expanded)
%              Number of leaves         :   37 ( 516 expanded)
%              Depth                    :   36
%              Number of atoms          : 1462 (25971 expanded)
%              Number of equality atoms :   25 ( 132 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X7 != X6 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ X18 )
      | ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X20 ) @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r2_hidden @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

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

thf('9',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( m2_connsp_2 @ X41 @ X40 @ X39 )
      | ( r1_tarski @ X39 @ ( k1_tops_1 @ X40 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ~ ( m2_connsp_2 @ sk_C_3 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_C_3 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('16',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ X34 )
      | ( ( k6_domain_1 @ X34 @ X35 )
        = ( k1_tarski @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('17',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 )
    | ( m2_connsp_2 @ sk_C_3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( m2_connsp_2 @ sk_C_3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
   <= ( m2_connsp_2 @ sk_C_3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( ( m2_connsp_2 @ sk_C_3 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C_3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['17','19'])).

thf('21',plain,
    ( ~ ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 )
    | ~ ( m2_connsp_2 @ sk_C_3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 )
    | ~ ( m2_connsp_2 @ sk_C_3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 )
   <= ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['18'])).

thf('24',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('25',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X37 ) )
      | ~ ( m1_connsp_2 @ X38 @ X37 @ X36 )
      | ( r2_hidden @ X36 @ ( k1_tops_1 @ X37 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_3 ) )
      | ~ ( m1_connsp_2 @ sk_C_3 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_3 ) )
      | ~ ( m1_connsp_2 @ sk_C_3 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C_3 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C_3 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C_3 ) )
   <= ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X20: $i,X21: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X20 ) @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r2_hidden @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('36',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ sk_C_3 ) ) )
   <= ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('37',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r1_tarski @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_C_3 ) )
   <= ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('40',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( r1_tarski @ X39 @ ( k1_tops_1 @ X40 @ X41 ) )
      | ( m2_connsp_2 @ X41 @ X40 @ X39 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ~ ( l1_pre_topc @ X40 )
      | ~ ( v2_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( ( m2_connsp_2 @ sk_C_3 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['38','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( m2_connsp_2 @ sk_C_3 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('49',plain,
    ( ~ ( m2_connsp_2 @ sk_C_3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
   <= ~ ( m2_connsp_2 @ sk_C_3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['21'])).

thf('50',plain,
    ( ( ~ ( m2_connsp_2 @ sk_C_3 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m2_connsp_2 @ sk_C_3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( m2_connsp_2 @ sk_C_3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      & ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( m2_connsp_2 @ sk_C_3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      & ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('53',plain,(
    ! [X33: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('54',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( m2_connsp_2 @ sk_C_3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      & ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('56',plain,(
    ! [X32: $i] :
      ( ( l1_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('57',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( m2_connsp_2 @ sk_C_3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      & ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( m2_connsp_2 @ sk_C_3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ~ ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( m2_connsp_2 @ sk_C_3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['18'])).

thf('62',plain,(
    m2_connsp_2 @ sk_C_3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['22','60','61'])).

thf('63',plain,
    ( ( m2_connsp_2 @ sk_C_3 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['20','62'])).

thf('64',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_C_3 ) ) ),
    inference(clc,[status(thm)],['14','63'])).

thf('65',plain,(
    ! [X24: $i,X26: $i] :
      ( ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('67',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( m1_subset_1 @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_3 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C_3 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','68'])).

thf('70',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ X18 )
      | ( r2_hidden @ X17 @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('71',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_3 ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( u1_struct_0 @ X37 ) )
      | ~ ( r2_hidden @ X36 @ ( k1_tops_1 @ X37 @ X38 ) )
      | ( m1_connsp_2 @ X38 @ X37 @ X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( l1_pre_topc @ X37 )
      | ~ ( v2_pre_topc @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C_3 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_3 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C_3 @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_3 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_3 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_3 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_C_3 ) ) ),
    inference(clc,[status(thm)],['14','63'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('82',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('83',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('84',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( r1_tarski @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['82','85'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('87',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X4 = X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('93',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('94',plain,(
    ! [X24: $i,X26: $i] :
      ( ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('95',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ X34 )
      | ( ( k6_domain_1 @ X34 @ X35 )
        = ( k1_tarski @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ ( k1_zfmisc_1 @ X0 ) @ k1_xboole_0 )
        = ( k1_tarski @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('99',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X14 )
      | ( X14
       != ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('100',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['98','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('103',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k6_domain_1 @ ( k1_zfmisc_1 @ X0 ) @ k1_xboole_0 )
      = ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['97','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k6_domain_1 @ ( k1_zfmisc_1 @ X0 ) @ k1_xboole_0 )
      = ( k1_tarski @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['97','103'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_domain_1 @ ( k1_zfmisc_1 @ X1 ) @ X0 )
        = ( k1_tarski @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X6: $i] :
      ( r2_hidden @ X6 @ ( k1_tarski @ X6 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('110',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( r1_tarski @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('111',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k6_domain_1 @ ( k1_zfmisc_1 @ X1 ) @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k6_domain_1 @ ( k1_zfmisc_1 @ X2 ) @ X1 ) @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['105','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ k1_xboole_0 ) @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','113'])).

thf('115',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['82','85'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ k1_xboole_0 ) @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['92','116'])).

thf('118',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_3 ) )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['81','117'])).

thf('119',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','118'])).

thf('120',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_3 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('122',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C_3 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','68'])).

thf('123',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X19 @ X18 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('124',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_3 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X19 @ X18 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('127',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_3 ) ) ),
    inference(clc,[status(thm)],['124','127'])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['121','128'])).

thf('130',plain,
    ( ~ ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 )
   <= ~ ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['21'])).

thf('131',plain,(
    ~ ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['22','60'])).

thf('132',plain,(
    ~ ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['129','132'])).

thf('134',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(clc,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['120','137'])).

thf('139',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(clc,[status(thm)],['135','136'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('141',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ sk_C_3 @ sk_A @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['138','141'])).

thf('143',plain,(
    ~ ( m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['130','131'])).

thf('144',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['139','140'])).

thf('145',plain,(
    ~ ( m1_connsp_2 @ sk_C_3 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['142','145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X33: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('150',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('152',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    $false ),
    inference(demod,[status(thm)],['0','152'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fD7ZHQbp2Q
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:07:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.12/2.31  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.12/2.31  % Solved by: fo/fo7.sh
% 2.12/2.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.12/2.31  % done 2573 iterations in 1.857s
% 2.12/2.31  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.12/2.31  % SZS output start Refutation
% 2.12/2.31  thf(sk_B_type, type, sk_B: $i > $i).
% 2.12/2.31  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.12/2.31  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.12/2.31  thf(sk_A_type, type, sk_A: $i).
% 2.12/2.31  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 2.12/2.31  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 2.12/2.31  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.12/2.31  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.12/2.31  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.12/2.31  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.12/2.31  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.12/2.31  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.12/2.31  thf(sk_C_3_type, type, sk_C_3: $i).
% 2.12/2.31  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.12/2.31  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 2.12/2.31  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 2.12/2.31  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.12/2.31  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.12/2.31  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.12/2.31  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.12/2.31  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.12/2.31  thf(t10_connsp_2, conjecture,
% 2.12/2.31    (![A:$i]:
% 2.12/2.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.12/2.31       ( ![B:$i]:
% 2.12/2.31         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.12/2.31           ( ![C:$i]:
% 2.12/2.31             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.12/2.31               ( ( m2_connsp_2 @
% 2.12/2.31                   C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 2.12/2.31                 ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ))).
% 2.12/2.31  thf(zf_stmt_0, negated_conjecture,
% 2.12/2.31    (~( ![A:$i]:
% 2.12/2.31        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 2.12/2.31            ( l1_pre_topc @ A ) ) =>
% 2.12/2.31          ( ![B:$i]:
% 2.12/2.31            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.12/2.31              ( ![C:$i]:
% 2.12/2.31                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.12/2.31                  ( ( m2_connsp_2 @
% 2.12/2.31                      C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 2.12/2.31                    ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ) )),
% 2.12/2.31    inference('cnf.neg', [status(esa)], [t10_connsp_2])).
% 2.12/2.31  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf(d1_tarski, axiom,
% 2.12/2.31    (![A:$i,B:$i]:
% 2.12/2.31     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 2.12/2.31       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 2.12/2.31  thf('1', plain,
% 2.12/2.31      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.12/2.31         (((X7) != (X6)) | (r2_hidden @ X7 @ X8) | ((X8) != (k1_tarski @ X6)))),
% 2.12/2.31      inference('cnf', [status(esa)], [d1_tarski])).
% 2.12/2.31  thf('2', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_tarski @ X6))),
% 2.12/2.31      inference('simplify', [status(thm)], ['1'])).
% 2.12/2.31  thf('3', plain,
% 2.12/2.31      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('4', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf(d2_subset_1, axiom,
% 2.12/2.31    (![A:$i,B:$i]:
% 2.12/2.31     ( ( ( v1_xboole_0 @ A ) =>
% 2.12/2.31         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 2.12/2.31       ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.12/2.31         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 2.12/2.31  thf('5', plain,
% 2.12/2.31      (![X17 : $i, X18 : $i]:
% 2.12/2.31         (~ (m1_subset_1 @ X17 @ X18)
% 2.12/2.31          | (r2_hidden @ X17 @ X18)
% 2.12/2.31          | (v1_xboole_0 @ X18))),
% 2.12/2.31      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.12/2.31  thf('6', plain,
% 2.12/2.31      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.12/2.31        | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['4', '5'])).
% 2.12/2.31  thf(t63_subset_1, axiom,
% 2.12/2.31    (![A:$i,B:$i]:
% 2.12/2.31     ( ( r2_hidden @ A @ B ) =>
% 2.12/2.31       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 2.12/2.31  thf('7', plain,
% 2.12/2.31      (![X20 : $i, X21 : $i]:
% 2.12/2.31         ((m1_subset_1 @ (k1_tarski @ X20) @ (k1_zfmisc_1 @ X21))
% 2.12/2.31          | ~ (r2_hidden @ X20 @ X21))),
% 2.12/2.31      inference('cnf', [status(esa)], [t63_subset_1])).
% 2.12/2.31  thf('8', plain,
% 2.12/2.31      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.12/2.31        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 2.12/2.31           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.12/2.31      inference('sup-', [status(thm)], ['6', '7'])).
% 2.12/2.31  thf(d2_connsp_2, axiom,
% 2.12/2.31    (![A:$i]:
% 2.12/2.31     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.12/2.31       ( ![B:$i]:
% 2.12/2.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.12/2.31           ( ![C:$i]:
% 2.12/2.31             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.12/2.31               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 2.12/2.31                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 2.12/2.31  thf('9', plain,
% 2.12/2.31      (![X39 : $i, X40 : $i, X41 : $i]:
% 2.12/2.31         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 2.12/2.31          | ~ (m2_connsp_2 @ X41 @ X40 @ X39)
% 2.12/2.31          | (r1_tarski @ X39 @ (k1_tops_1 @ X40 @ X41))
% 2.12/2.31          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 2.12/2.31          | ~ (l1_pre_topc @ X40)
% 2.12/2.31          | ~ (v2_pre_topc @ X40))),
% 2.12/2.31      inference('cnf', [status(esa)], [d2_connsp_2])).
% 2.12/2.31  thf('10', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.12/2.31          | ~ (v2_pre_topc @ sk_A)
% 2.12/2.31          | ~ (l1_pre_topc @ sk_A)
% 2.12/2.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.12/2.31          | (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ X0))
% 2.12/2.31          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B_1)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['8', '9'])).
% 2.12/2.31  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('13', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.12/2.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.12/2.31          | (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ X0))
% 2.12/2.31          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B_1)))),
% 2.12/2.31      inference('demod', [status(thm)], ['10', '11', '12'])).
% 2.12/2.31  thf('14', plain,
% 2.12/2.31      ((~ (m2_connsp_2 @ sk_C_3 @ sk_A @ (k1_tarski @ sk_B_1))
% 2.12/2.31        | (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_C_3))
% 2.12/2.31        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['3', '13'])).
% 2.12/2.31  thf('15', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf(redefinition_k6_domain_1, axiom,
% 2.12/2.31    (![A:$i,B:$i]:
% 2.12/2.31     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 2.12/2.31       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 2.12/2.31  thf('16', plain,
% 2.12/2.31      (![X34 : $i, X35 : $i]:
% 2.12/2.31         ((v1_xboole_0 @ X34)
% 2.12/2.31          | ~ (m1_subset_1 @ X35 @ X34)
% 2.12/2.31          | ((k6_domain_1 @ X34 @ X35) = (k1_tarski @ X35)))),
% 2.12/2.31      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 2.12/2.31  thf('17', plain,
% 2.12/2.31      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 2.12/2.31        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['15', '16'])).
% 2.12/2.31  thf('18', plain,
% 2.12/2.31      (((m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1)
% 2.12/2.31        | (m2_connsp_2 @ sk_C_3 @ sk_A @ 
% 2.12/2.31           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('19', plain,
% 2.12/2.31      (((m2_connsp_2 @ sk_C_3 @ sk_A @ 
% 2.12/2.31         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 2.12/2.31         <= (((m2_connsp_2 @ sk_C_3 @ sk_A @ 
% 2.12/2.31               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 2.12/2.31      inference('split', [status(esa)], ['18'])).
% 2.12/2.31  thf('20', plain,
% 2.12/2.31      ((((m2_connsp_2 @ sk_C_3 @ sk_A @ (k1_tarski @ sk_B_1))
% 2.12/2.31         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 2.12/2.31         <= (((m2_connsp_2 @ sk_C_3 @ sk_A @ 
% 2.12/2.31               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 2.12/2.31      inference('sup+', [status(thm)], ['17', '19'])).
% 2.12/2.31  thf('21', plain,
% 2.12/2.31      ((~ (m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1)
% 2.12/2.31        | ~ (m2_connsp_2 @ sk_C_3 @ sk_A @ 
% 2.12/2.31             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('22', plain,
% 2.12/2.31      (~ ((m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1)) | 
% 2.12/2.31       ~
% 2.12/2.31       ((m2_connsp_2 @ sk_C_3 @ sk_A @ 
% 2.12/2.31         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 2.12/2.31      inference('split', [status(esa)], ['21'])).
% 2.12/2.31  thf('23', plain,
% 2.12/2.31      (((m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1))
% 2.12/2.31         <= (((m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1)))),
% 2.12/2.31      inference('split', [status(esa)], ['18'])).
% 2.12/2.31  thf('24', plain,
% 2.12/2.31      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf(d1_connsp_2, axiom,
% 2.12/2.31    (![A:$i]:
% 2.12/2.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.12/2.31       ( ![B:$i]:
% 2.12/2.31         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.12/2.31           ( ![C:$i]:
% 2.12/2.31             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.12/2.31               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 2.12/2.31                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 2.12/2.31  thf('25', plain,
% 2.12/2.31      (![X36 : $i, X37 : $i, X38 : $i]:
% 2.12/2.31         (~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X37))
% 2.12/2.31          | ~ (m1_connsp_2 @ X38 @ X37 @ X36)
% 2.12/2.31          | (r2_hidden @ X36 @ (k1_tops_1 @ X37 @ X38))
% 2.12/2.31          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 2.12/2.31          | ~ (l1_pre_topc @ X37)
% 2.12/2.31          | ~ (v2_pre_topc @ X37)
% 2.12/2.31          | (v2_struct_0 @ X37))),
% 2.12/2.31      inference('cnf', [status(esa)], [d1_connsp_2])).
% 2.12/2.31  thf('26', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         ((v2_struct_0 @ sk_A)
% 2.12/2.31          | ~ (v2_pre_topc @ sk_A)
% 2.12/2.31          | ~ (l1_pre_topc @ sk_A)
% 2.12/2.31          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_3))
% 2.12/2.31          | ~ (m1_connsp_2 @ sk_C_3 @ sk_A @ X0)
% 2.12/2.31          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['24', '25'])).
% 2.12/2.31  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('29', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         ((v2_struct_0 @ sk_A)
% 2.12/2.31          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_3))
% 2.12/2.31          | ~ (m1_connsp_2 @ sk_C_3 @ sk_A @ X0)
% 2.12/2.31          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.12/2.31      inference('demod', [status(thm)], ['26', '27', '28'])).
% 2.12/2.31  thf('30', plain,
% 2.12/2.31      (((~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 2.12/2.31         | (r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C_3))
% 2.12/2.31         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['23', '29'])).
% 2.12/2.31  thf('31', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('32', plain,
% 2.12/2.31      ((((r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C_3))
% 2.12/2.31         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1)))),
% 2.12/2.31      inference('demod', [status(thm)], ['30', '31'])).
% 2.12/2.31  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('34', plain,
% 2.12/2.31      (((r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C_3)))
% 2.12/2.31         <= (((m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1)))),
% 2.12/2.31      inference('clc', [status(thm)], ['32', '33'])).
% 2.12/2.31  thf('35', plain,
% 2.12/2.31      (![X20 : $i, X21 : $i]:
% 2.12/2.31         ((m1_subset_1 @ (k1_tarski @ X20) @ (k1_zfmisc_1 @ X21))
% 2.12/2.31          | ~ (r2_hidden @ X20 @ X21))),
% 2.12/2.31      inference('cnf', [status(esa)], [t63_subset_1])).
% 2.12/2.31  thf('36', plain,
% 2.12/2.31      (((m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 2.12/2.31         (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ sk_C_3))))
% 2.12/2.31         <= (((m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['34', '35'])).
% 2.12/2.31  thf(t3_subset, axiom,
% 2.12/2.31    (![A:$i,B:$i]:
% 2.12/2.31     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.12/2.31  thf('37', plain,
% 2.12/2.31      (![X24 : $i, X25 : $i]:
% 2.12/2.31         ((r1_tarski @ X24 @ X25) | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25)))),
% 2.12/2.31      inference('cnf', [status(esa)], [t3_subset])).
% 2.12/2.31  thf('38', plain,
% 2.12/2.31      (((r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_C_3)))
% 2.12/2.31         <= (((m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['36', '37'])).
% 2.12/2.31  thf('39', plain,
% 2.12/2.31      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.12/2.31        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 2.12/2.31           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.12/2.31      inference('sup-', [status(thm)], ['6', '7'])).
% 2.12/2.31  thf('40', plain,
% 2.12/2.31      (![X39 : $i, X40 : $i, X41 : $i]:
% 2.12/2.31         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 2.12/2.31          | ~ (r1_tarski @ X39 @ (k1_tops_1 @ X40 @ X41))
% 2.12/2.31          | (m2_connsp_2 @ X41 @ X40 @ X39)
% 2.12/2.31          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 2.12/2.31          | ~ (l1_pre_topc @ X40)
% 2.12/2.31          | ~ (v2_pre_topc @ X40))),
% 2.12/2.31      inference('cnf', [status(esa)], [d2_connsp_2])).
% 2.12/2.31  thf('41', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.12/2.31          | ~ (v2_pre_topc @ sk_A)
% 2.12/2.31          | ~ (l1_pre_topc @ sk_A)
% 2.12/2.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.12/2.31          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B_1))
% 2.12/2.31          | ~ (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ X0)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['39', '40'])).
% 2.12/2.31  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('44', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.12/2.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.12/2.31          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B_1))
% 2.12/2.31          | ~ (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ X0)))),
% 2.12/2.31      inference('demod', [status(thm)], ['41', '42', '43'])).
% 2.12/2.31  thf('45', plain,
% 2.12/2.31      ((((m2_connsp_2 @ sk_C_3 @ sk_A @ (k1_tarski @ sk_B_1))
% 2.12/2.31         | ~ (m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.12/2.31         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 2.12/2.31         <= (((m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['38', '44'])).
% 2.12/2.31  thf('46', plain,
% 2.12/2.31      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('47', plain,
% 2.12/2.31      ((((m2_connsp_2 @ sk_C_3 @ sk_A @ (k1_tarski @ sk_B_1))
% 2.12/2.31         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 2.12/2.31         <= (((m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1)))),
% 2.12/2.31      inference('demod', [status(thm)], ['45', '46'])).
% 2.12/2.31  thf('48', plain,
% 2.12/2.31      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 2.12/2.31        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['15', '16'])).
% 2.12/2.31  thf('49', plain,
% 2.12/2.31      ((~ (m2_connsp_2 @ sk_C_3 @ sk_A @ 
% 2.12/2.31           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 2.12/2.31         <= (~
% 2.12/2.31             ((m2_connsp_2 @ sk_C_3 @ sk_A @ 
% 2.12/2.31               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 2.12/2.31      inference('split', [status(esa)], ['21'])).
% 2.12/2.31  thf('50', plain,
% 2.12/2.31      (((~ (m2_connsp_2 @ sk_C_3 @ sk_A @ (k1_tarski @ sk_B_1))
% 2.12/2.31         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 2.12/2.31         <= (~
% 2.12/2.31             ((m2_connsp_2 @ sk_C_3 @ sk_A @ 
% 2.12/2.31               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 2.12/2.31      inference('sup-', [status(thm)], ['48', '49'])).
% 2.12/2.31  thf('51', plain,
% 2.12/2.31      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.12/2.31         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 2.12/2.31         <= (~
% 2.12/2.31             ((m2_connsp_2 @ sk_C_3 @ sk_A @ 
% 2.12/2.31               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) & 
% 2.12/2.31             ((m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['47', '50'])).
% 2.12/2.31  thf('52', plain,
% 2.12/2.31      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 2.12/2.31         <= (~
% 2.12/2.31             ((m2_connsp_2 @ sk_C_3 @ sk_A @ 
% 2.12/2.31               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) & 
% 2.12/2.31             ((m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1)))),
% 2.12/2.31      inference('simplify', [status(thm)], ['51'])).
% 2.12/2.31  thf(fc2_struct_0, axiom,
% 2.12/2.31    (![A:$i]:
% 2.12/2.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 2.12/2.31       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.12/2.31  thf('53', plain,
% 2.12/2.31      (![X33 : $i]:
% 2.12/2.31         (~ (v1_xboole_0 @ (u1_struct_0 @ X33))
% 2.12/2.31          | ~ (l1_struct_0 @ X33)
% 2.12/2.31          | (v2_struct_0 @ X33))),
% 2.12/2.31      inference('cnf', [status(esa)], [fc2_struct_0])).
% 2.12/2.31  thf('54', plain,
% 2.12/2.31      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 2.12/2.31         <= (~
% 2.12/2.31             ((m2_connsp_2 @ sk_C_3 @ sk_A @ 
% 2.12/2.31               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) & 
% 2.12/2.31             ((m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['52', '53'])).
% 2.12/2.31  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf(dt_l1_pre_topc, axiom,
% 2.12/2.31    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 2.12/2.31  thf('56', plain,
% 2.12/2.31      (![X32 : $i]: ((l1_struct_0 @ X32) | ~ (l1_pre_topc @ X32))),
% 2.12/2.31      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 2.12/2.31  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 2.12/2.31      inference('sup-', [status(thm)], ['55', '56'])).
% 2.12/2.31  thf('58', plain,
% 2.12/2.31      (((v2_struct_0 @ sk_A))
% 2.12/2.31         <= (~
% 2.12/2.31             ((m2_connsp_2 @ sk_C_3 @ sk_A @ 
% 2.12/2.31               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) & 
% 2.12/2.31             ((m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1)))),
% 2.12/2.31      inference('demod', [status(thm)], ['54', '57'])).
% 2.12/2.31  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('60', plain,
% 2.12/2.31      (((m2_connsp_2 @ sk_C_3 @ sk_A @ 
% 2.12/2.31         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) | 
% 2.12/2.31       ~ ((m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1))),
% 2.12/2.31      inference('sup-', [status(thm)], ['58', '59'])).
% 2.12/2.31  thf('61', plain,
% 2.12/2.31      (((m2_connsp_2 @ sk_C_3 @ sk_A @ 
% 2.12/2.31         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) | 
% 2.12/2.31       ((m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1))),
% 2.12/2.31      inference('split', [status(esa)], ['18'])).
% 2.12/2.31  thf('62', plain,
% 2.12/2.31      (((m2_connsp_2 @ sk_C_3 @ sk_A @ 
% 2.12/2.31         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 2.12/2.31      inference('sat_resolution*', [status(thm)], ['22', '60', '61'])).
% 2.12/2.31  thf('63', plain,
% 2.12/2.31      (((m2_connsp_2 @ sk_C_3 @ sk_A @ (k1_tarski @ sk_B_1))
% 2.12/2.31        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 2.12/2.31      inference('simpl_trail', [status(thm)], ['20', '62'])).
% 2.12/2.31  thf('64', plain,
% 2.12/2.31      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.12/2.31        | (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_C_3)))),
% 2.12/2.31      inference('clc', [status(thm)], ['14', '63'])).
% 2.12/2.31  thf('65', plain,
% 2.12/2.31      (![X24 : $i, X26 : $i]:
% 2.12/2.31         ((m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X26)) | ~ (r1_tarski @ X24 @ X26))),
% 2.12/2.31      inference('cnf', [status(esa)], [t3_subset])).
% 2.12/2.31  thf('66', plain,
% 2.12/2.31      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.12/2.31        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 2.12/2.31           (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ sk_C_3))))),
% 2.12/2.31      inference('sup-', [status(thm)], ['64', '65'])).
% 2.12/2.31  thf(t4_subset, axiom,
% 2.12/2.31    (![A:$i,B:$i,C:$i]:
% 2.12/2.31     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 2.12/2.31       ( m1_subset_1 @ A @ C ) ))).
% 2.12/2.31  thf('67', plain,
% 2.12/2.31      (![X27 : $i, X28 : $i, X29 : $i]:
% 2.12/2.31         (~ (r2_hidden @ X27 @ X28)
% 2.12/2.31          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X29))
% 2.12/2.31          | (m1_subset_1 @ X27 @ X29))),
% 2.12/2.31      inference('cnf', [status(esa)], [t4_subset])).
% 2.12/2.31  thf('68', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.12/2.31          | (m1_subset_1 @ X0 @ (k1_tops_1 @ sk_A @ sk_C_3))
% 2.12/2.31          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B_1)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['66', '67'])).
% 2.12/2.31  thf('69', plain,
% 2.12/2.31      (((m1_subset_1 @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C_3))
% 2.12/2.31        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['2', '68'])).
% 2.12/2.31  thf('70', plain,
% 2.12/2.31      (![X17 : $i, X18 : $i]:
% 2.12/2.31         (~ (m1_subset_1 @ X17 @ X18)
% 2.12/2.31          | (r2_hidden @ X17 @ X18)
% 2.12/2.31          | (v1_xboole_0 @ X18))),
% 2.12/2.31      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.12/2.31  thf('71', plain,
% 2.12/2.31      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.12/2.31        | (v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_3))
% 2.12/2.31        | (r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C_3)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['69', '70'])).
% 2.12/2.31  thf('72', plain,
% 2.12/2.31      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('73', plain,
% 2.12/2.31      (![X36 : $i, X37 : $i, X38 : $i]:
% 2.12/2.31         (~ (m1_subset_1 @ X36 @ (u1_struct_0 @ X37))
% 2.12/2.31          | ~ (r2_hidden @ X36 @ (k1_tops_1 @ X37 @ X38))
% 2.12/2.31          | (m1_connsp_2 @ X38 @ X37 @ X36)
% 2.12/2.31          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 2.12/2.31          | ~ (l1_pre_topc @ X37)
% 2.12/2.31          | ~ (v2_pre_topc @ X37)
% 2.12/2.31          | (v2_struct_0 @ X37))),
% 2.12/2.31      inference('cnf', [status(esa)], [d1_connsp_2])).
% 2.12/2.31  thf('74', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         ((v2_struct_0 @ sk_A)
% 2.12/2.31          | ~ (v2_pre_topc @ sk_A)
% 2.12/2.31          | ~ (l1_pre_topc @ sk_A)
% 2.12/2.31          | (m1_connsp_2 @ sk_C_3 @ sk_A @ X0)
% 2.12/2.31          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_3))
% 2.12/2.31          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['72', '73'])).
% 2.12/2.31  thf('75', plain, ((v2_pre_topc @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('77', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         ((v2_struct_0 @ sk_A)
% 2.12/2.31          | (m1_connsp_2 @ sk_C_3 @ sk_A @ X0)
% 2.12/2.31          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_3))
% 2.12/2.31          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 2.12/2.31      inference('demod', [status(thm)], ['74', '75', '76'])).
% 2.12/2.31  thf('78', plain,
% 2.12/2.31      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_3))
% 2.12/2.31        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.12/2.31        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 2.12/2.31        | (m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1)
% 2.12/2.31        | (v2_struct_0 @ sk_A))),
% 2.12/2.31      inference('sup-', [status(thm)], ['71', '77'])).
% 2.12/2.31  thf('79', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('80', plain,
% 2.12/2.31      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_3))
% 2.12/2.31        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.12/2.31        | (m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1)
% 2.12/2.31        | (v2_struct_0 @ sk_A))),
% 2.12/2.31      inference('demod', [status(thm)], ['78', '79'])).
% 2.12/2.31  thf('81', plain,
% 2.12/2.31      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.12/2.31        | (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_C_3)))),
% 2.12/2.31      inference('clc', [status(thm)], ['14', '63'])).
% 2.12/2.31  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.12/2.31  thf('82', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 2.12/2.31      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.12/2.31  thf(d1_xboole_0, axiom,
% 2.12/2.31    (![A:$i]:
% 2.12/2.31     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.12/2.31  thf('83', plain,
% 2.12/2.31      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.12/2.31      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.12/2.31  thf(t7_ordinal1, axiom,
% 2.12/2.31    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.12/2.31  thf('84', plain,
% 2.12/2.31      (![X30 : $i, X31 : $i]:
% 2.12/2.31         (~ (r2_hidden @ X30 @ X31) | ~ (r1_tarski @ X31 @ X30))),
% 2.12/2.31      inference('cnf', [status(esa)], [t7_ordinal1])).
% 2.12/2.31  thf('85', plain,
% 2.12/2.31      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['83', '84'])).
% 2.12/2.31  thf('86', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.12/2.31      inference('sup-', [status(thm)], ['82', '85'])).
% 2.12/2.31  thf(t2_tarski, axiom,
% 2.12/2.31    (![A:$i,B:$i]:
% 2.12/2.31     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 2.12/2.31       ( ( A ) = ( B ) ) ))).
% 2.12/2.31  thf('87', plain,
% 2.12/2.31      (![X3 : $i, X4 : $i]:
% 2.12/2.31         (((X4) = (X3))
% 2.12/2.31          | (r2_hidden @ (sk_C @ X3 @ X4) @ X3)
% 2.12/2.31          | (r2_hidden @ (sk_C @ X3 @ X4) @ X4))),
% 2.12/2.31      inference('cnf', [status(esa)], [t2_tarski])).
% 2.12/2.31  thf('88', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.12/2.31      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.12/2.31  thf('89', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         ((r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 2.12/2.31          | ((X1) = (X0))
% 2.12/2.31          | ~ (v1_xboole_0 @ X0))),
% 2.12/2.31      inference('sup-', [status(thm)], ['87', '88'])).
% 2.12/2.31  thf('90', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.12/2.31      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.12/2.31  thf('91', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         (~ (v1_xboole_0 @ X1) | ((X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 2.12/2.31      inference('sup-', [status(thm)], ['89', '90'])).
% 2.12/2.31  thf('92', plain,
% 2.12/2.31      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['86', '91'])).
% 2.12/2.31  thf('93', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 2.12/2.31      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.12/2.31  thf('94', plain,
% 2.12/2.31      (![X24 : $i, X26 : $i]:
% 2.12/2.31         ((m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X26)) | ~ (r1_tarski @ X24 @ X26))),
% 2.12/2.31      inference('cnf', [status(esa)], [t3_subset])).
% 2.12/2.31  thf('95', plain,
% 2.12/2.31      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 2.12/2.31      inference('sup-', [status(thm)], ['93', '94'])).
% 2.12/2.31  thf('96', plain,
% 2.12/2.31      (![X34 : $i, X35 : $i]:
% 2.12/2.31         ((v1_xboole_0 @ X34)
% 2.12/2.31          | ~ (m1_subset_1 @ X35 @ X34)
% 2.12/2.31          | ((k6_domain_1 @ X34 @ X35) = (k1_tarski @ X35)))),
% 2.12/2.31      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 2.12/2.31  thf('97', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         (((k6_domain_1 @ (k1_zfmisc_1 @ X0) @ k1_xboole_0)
% 2.12/2.31            = (k1_tarski @ k1_xboole_0))
% 2.12/2.31          | (v1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['95', '96'])).
% 2.12/2.31  thf('98', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 2.12/2.31      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.12/2.31  thf(d1_zfmisc_1, axiom,
% 2.12/2.31    (![A:$i,B:$i]:
% 2.12/2.31     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 2.12/2.31       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 2.12/2.31  thf('99', plain,
% 2.12/2.31      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.12/2.31         (~ (r1_tarski @ X12 @ X13)
% 2.12/2.31          | (r2_hidden @ X12 @ X14)
% 2.12/2.31          | ((X14) != (k1_zfmisc_1 @ X13)))),
% 2.12/2.31      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 2.12/2.31  thf('100', plain,
% 2.12/2.31      (![X12 : $i, X13 : $i]:
% 2.12/2.31         ((r2_hidden @ X12 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X12 @ X13))),
% 2.12/2.31      inference('simplify', [status(thm)], ['99'])).
% 2.12/2.31  thf('101', plain,
% 2.12/2.31      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 2.12/2.31      inference('sup-', [status(thm)], ['98', '100'])).
% 2.12/2.31  thf('102', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.12/2.31      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.12/2.31  thf('103', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 2.12/2.31      inference('sup-', [status(thm)], ['101', '102'])).
% 2.12/2.31  thf('104', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         ((k6_domain_1 @ (k1_zfmisc_1 @ X0) @ k1_xboole_0)
% 2.12/2.31           = (k1_tarski @ k1_xboole_0))),
% 2.12/2.31      inference('clc', [status(thm)], ['97', '103'])).
% 2.12/2.31  thf('105', plain,
% 2.12/2.31      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['86', '91'])).
% 2.12/2.31  thf('106', plain,
% 2.12/2.31      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['86', '91'])).
% 2.12/2.31  thf('107', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         ((k6_domain_1 @ (k1_zfmisc_1 @ X0) @ k1_xboole_0)
% 2.12/2.31           = (k1_tarski @ k1_xboole_0))),
% 2.12/2.31      inference('clc', [status(thm)], ['97', '103'])).
% 2.12/2.31  thf('108', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         (((k6_domain_1 @ (k1_zfmisc_1 @ X1) @ X0) = (k1_tarski @ k1_xboole_0))
% 2.12/2.31          | ~ (v1_xboole_0 @ X0))),
% 2.12/2.31      inference('sup+', [status(thm)], ['106', '107'])).
% 2.12/2.31  thf('109', plain, (![X6 : $i]: (r2_hidden @ X6 @ (k1_tarski @ X6))),
% 2.12/2.31      inference('simplify', [status(thm)], ['1'])).
% 2.12/2.31  thf('110', plain,
% 2.12/2.31      (![X30 : $i, X31 : $i]:
% 2.12/2.31         (~ (r2_hidden @ X30 @ X31) | ~ (r1_tarski @ X31 @ X30))),
% 2.12/2.31      inference('cnf', [status(esa)], [t7_ordinal1])).
% 2.12/2.31  thf('111', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 2.12/2.31      inference('sup-', [status(thm)], ['109', '110'])).
% 2.12/2.31  thf('112', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         (~ (r1_tarski @ (k6_domain_1 @ (k1_zfmisc_1 @ X1) @ X0) @ k1_xboole_0)
% 2.12/2.31          | ~ (v1_xboole_0 @ X0))),
% 2.12/2.31      inference('sup-', [status(thm)], ['108', '111'])).
% 2.12/2.31  thf('113', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.31         (~ (r1_tarski @ (k6_domain_1 @ (k1_zfmisc_1 @ X2) @ X1) @ X0)
% 2.12/2.31          | ~ (v1_xboole_0 @ X0)
% 2.12/2.31          | ~ (v1_xboole_0 @ X1))),
% 2.12/2.31      inference('sup-', [status(thm)], ['105', '112'])).
% 2.12/2.31  thf('114', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         (~ (r1_tarski @ (k1_tarski @ k1_xboole_0) @ X0)
% 2.12/2.31          | ~ (v1_xboole_0 @ k1_xboole_0)
% 2.12/2.31          | ~ (v1_xboole_0 @ X0))),
% 2.12/2.31      inference('sup-', [status(thm)], ['104', '113'])).
% 2.12/2.31  thf('115', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.12/2.31      inference('sup-', [status(thm)], ['82', '85'])).
% 2.12/2.31  thf('116', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         (~ (r1_tarski @ (k1_tarski @ k1_xboole_0) @ X0) | ~ (v1_xboole_0 @ X0))),
% 2.12/2.31      inference('demod', [status(thm)], ['114', '115'])).
% 2.12/2.31  thf('117', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         (~ (r1_tarski @ (k1_tarski @ X0) @ X1)
% 2.12/2.31          | ~ (v1_xboole_0 @ X0)
% 2.12/2.31          | ~ (v1_xboole_0 @ X1))),
% 2.12/2.31      inference('sup-', [status(thm)], ['92', '116'])).
% 2.12/2.31  thf('118', plain,
% 2.12/2.31      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.12/2.31        | ~ (v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_3))
% 2.12/2.31        | ~ (v1_xboole_0 @ sk_B_1))),
% 2.12/2.31      inference('sup-', [status(thm)], ['81', '117'])).
% 2.12/2.31  thf('119', plain,
% 2.12/2.31      (((v2_struct_0 @ sk_A)
% 2.12/2.31        | (m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1)
% 2.12/2.31        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.12/2.31        | ~ (v1_xboole_0 @ sk_B_1)
% 2.12/2.31        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['80', '118'])).
% 2.12/2.31  thf('120', plain,
% 2.12/2.31      ((~ (v1_xboole_0 @ sk_B_1)
% 2.12/2.31        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.12/2.31        | (m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1)
% 2.12/2.31        | (v2_struct_0 @ sk_A))),
% 2.12/2.31      inference('simplify', [status(thm)], ['119'])).
% 2.12/2.31  thf('121', plain,
% 2.12/2.31      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_3))
% 2.12/2.31        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.12/2.31        | (m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1)
% 2.12/2.31        | (v2_struct_0 @ sk_A))),
% 2.12/2.31      inference('demod', [status(thm)], ['78', '79'])).
% 2.12/2.31  thf('122', plain,
% 2.12/2.31      (((m1_subset_1 @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C_3))
% 2.12/2.31        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['2', '68'])).
% 2.12/2.31  thf('123', plain,
% 2.12/2.31      (![X18 : $i, X19 : $i]:
% 2.12/2.31         (~ (m1_subset_1 @ X19 @ X18)
% 2.12/2.31          | (v1_xboole_0 @ X19)
% 2.12/2.31          | ~ (v1_xboole_0 @ X18))),
% 2.12/2.31      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.12/2.31  thf('124', plain,
% 2.12/2.31      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.12/2.31        | ~ (v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_3))
% 2.12/2.31        | (v1_xboole_0 @ sk_B_1))),
% 2.12/2.31      inference('sup-', [status(thm)], ['122', '123'])).
% 2.12/2.31  thf('125', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('126', plain,
% 2.12/2.31      (![X18 : $i, X19 : $i]:
% 2.12/2.31         (~ (m1_subset_1 @ X19 @ X18)
% 2.12/2.31          | (v1_xboole_0 @ X19)
% 2.12/2.31          | ~ (v1_xboole_0 @ X18))),
% 2.12/2.31      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.12/2.31  thf('127', plain,
% 2.12/2.31      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 2.12/2.31      inference('sup-', [status(thm)], ['125', '126'])).
% 2.12/2.31  thf('128', plain,
% 2.12/2.31      (((v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_3)))),
% 2.12/2.31      inference('clc', [status(thm)], ['124', '127'])).
% 2.12/2.31  thf('129', plain,
% 2.12/2.31      (((v2_struct_0 @ sk_A)
% 2.12/2.31        | (m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1)
% 2.12/2.31        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.12/2.31        | (v1_xboole_0 @ sk_B_1))),
% 2.12/2.31      inference('sup-', [status(thm)], ['121', '128'])).
% 2.12/2.31  thf('130', plain,
% 2.12/2.31      ((~ (m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1))
% 2.12/2.31         <= (~ ((m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1)))),
% 2.12/2.31      inference('split', [status(esa)], ['21'])).
% 2.12/2.31  thf('131', plain, (~ ((m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1))),
% 2.12/2.31      inference('sat_resolution*', [status(thm)], ['22', '60'])).
% 2.12/2.31  thf('132', plain, (~ (m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1)),
% 2.12/2.31      inference('simpl_trail', [status(thm)], ['130', '131'])).
% 2.12/2.31  thf('133', plain,
% 2.12/2.31      (((v1_xboole_0 @ sk_B_1)
% 2.12/2.31        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.12/2.31        | (v2_struct_0 @ sk_A))),
% 2.12/2.31      inference('sup-', [status(thm)], ['129', '132'])).
% 2.12/2.31  thf('134', plain,
% 2.12/2.31      ((~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 2.12/2.31      inference('sup-', [status(thm)], ['125', '126'])).
% 2.12/2.31  thf('135', plain, (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 2.12/2.31      inference('clc', [status(thm)], ['133', '134'])).
% 2.12/2.31  thf('136', plain, (~ (v2_struct_0 @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('137', plain, ((v1_xboole_0 @ sk_B_1)),
% 2.12/2.31      inference('clc', [status(thm)], ['135', '136'])).
% 2.12/2.31  thf('138', plain,
% 2.12/2.31      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.12/2.31        | (m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1)
% 2.12/2.31        | (v2_struct_0 @ sk_A))),
% 2.12/2.31      inference('demod', [status(thm)], ['120', '137'])).
% 2.12/2.31  thf('139', plain, ((v1_xboole_0 @ sk_B_1)),
% 2.12/2.31      inference('clc', [status(thm)], ['135', '136'])).
% 2.12/2.31  thf('140', plain,
% 2.12/2.31      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['86', '91'])).
% 2.12/2.31  thf('141', plain, (((sk_B_1) = (k1_xboole_0))),
% 2.12/2.31      inference('sup-', [status(thm)], ['139', '140'])).
% 2.12/2.31  thf('142', plain,
% 2.12/2.31      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 2.12/2.31        | (m1_connsp_2 @ sk_C_3 @ sk_A @ k1_xboole_0)
% 2.12/2.31        | (v2_struct_0 @ sk_A))),
% 2.12/2.31      inference('demod', [status(thm)], ['138', '141'])).
% 2.12/2.31  thf('143', plain, (~ (m1_connsp_2 @ sk_C_3 @ sk_A @ sk_B_1)),
% 2.12/2.31      inference('simpl_trail', [status(thm)], ['130', '131'])).
% 2.12/2.31  thf('144', plain, (((sk_B_1) = (k1_xboole_0))),
% 2.12/2.31      inference('sup-', [status(thm)], ['139', '140'])).
% 2.12/2.31  thf('145', plain, (~ (m1_connsp_2 @ sk_C_3 @ sk_A @ k1_xboole_0)),
% 2.12/2.31      inference('demod', [status(thm)], ['143', '144'])).
% 2.12/2.31  thf('146', plain,
% 2.12/2.31      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 2.12/2.31      inference('clc', [status(thm)], ['142', '145'])).
% 2.12/2.31  thf('147', plain, (~ (v2_struct_0 @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('148', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 2.12/2.31      inference('clc', [status(thm)], ['146', '147'])).
% 2.12/2.31  thf('149', plain,
% 2.12/2.31      (![X33 : $i]:
% 2.12/2.31         (~ (v1_xboole_0 @ (u1_struct_0 @ X33))
% 2.12/2.31          | ~ (l1_struct_0 @ X33)
% 2.12/2.31          | (v2_struct_0 @ X33))),
% 2.12/2.31      inference('cnf', [status(esa)], [fc2_struct_0])).
% 2.12/2.31  thf('150', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 2.12/2.31      inference('sup-', [status(thm)], ['148', '149'])).
% 2.12/2.31  thf('151', plain, ((l1_struct_0 @ sk_A)),
% 2.12/2.31      inference('sup-', [status(thm)], ['55', '56'])).
% 2.12/2.31  thf('152', plain, ((v2_struct_0 @ sk_A)),
% 2.12/2.31      inference('demod', [status(thm)], ['150', '151'])).
% 2.12/2.31  thf('153', plain, ($false), inference('demod', [status(thm)], ['0', '152'])).
% 2.12/2.31  
% 2.12/2.31  % SZS output end Refutation
% 2.12/2.31  
% 2.12/2.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
