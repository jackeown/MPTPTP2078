%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jeNehU2P6L

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:00 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 231 expanded)
%              Number of leaves         :   28 (  76 expanded)
%              Depth                    :   19
%              Number of atoms          : 1076 (3404 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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
    ! [X36: $i,X37: $i] :
      ( ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ X36 )
      | ( ( k6_domain_1 @ X36 @ X37 )
        = ( k1_tarski @ X37 ) ) ) ),
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

thf('9',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X34: $i,X35: $i] :
      ( ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ X34 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X34 @ X35 ) @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

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

thf('15',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( m2_connsp_2 @ X43 @ X42 @ X41 )
      | ( r1_tarski @ X41 @ ( k1_tops_1 @ X42 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf('21',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','20'])).

thf('22',plain,
    ( ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ X28 @ X29 )
      | ~ ( r1_tarski @ ( k2_tarski @ X28 @ X30 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
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

thf('28',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X39 ) )
      | ~ ( r2_hidden @ X38 @ ( k1_tops_1 @ X39 @ X40 ) )
      | ( m1_connsp_2 @ X40 @ X39 @ X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('40',plain,(
    ! [X33: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('41',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('43',plain,(
    ! [X32: $i] :
      ( ( l1_struct_0 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('44',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
      & ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('49',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X39 ) )
      | ~ ( m1_connsp_2 @ X40 @ X39 @ X38 )
      | ( r2_hidden @ X38 @ ( k1_tops_1 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ~ ( l1_pre_topc @ X39 )
      | ~ ( v2_pre_topc @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['49','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('62',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X28 @ X30 ) @ X31 )
      | ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( r2_hidden @ X28 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
        | ( r1_tarski @ ( k2_tarski @ X0 @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_B @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('66',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('68',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( r1_tarski @ X41 @ ( k1_tops_1 @ X42 @ X43 ) )
      | ( m2_connsp_2 @ X43 @ X42 @ X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X42 )
      | ~ ( v2_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['66','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('77',plain,
    ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('78',plain,
    ( ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X33: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('82',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['42','43'])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','47','48','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jeNehU2P6L
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:38:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.35/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.52  % Solved by: fo/fo7.sh
% 0.35/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.52  % done 135 iterations in 0.062s
% 0.35/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.52  % SZS output start Refutation
% 0.35/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.35/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.35/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.52  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.35/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.52  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.35/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.35/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.35/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.52  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.35/0.52  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.35/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.35/0.52  thf(t10_connsp_2, conjecture,
% 0.35/0.52    (![A:$i]:
% 0.35/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.52       ( ![B:$i]:
% 0.35/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.52           ( ![C:$i]:
% 0.35/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.52               ( ( m2_connsp_2 @
% 0.35/0.52                   C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.35/0.52                 ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ))).
% 0.35/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.52    (~( ![A:$i]:
% 0.35/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.35/0.52            ( l1_pre_topc @ A ) ) =>
% 0.35/0.52          ( ![B:$i]:
% 0.35/0.52            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.52              ( ![C:$i]:
% 0.35/0.52                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.52                  ( ( m2_connsp_2 @
% 0.35/0.52                      C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.35/0.52                    ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ) )),
% 0.35/0.52    inference('cnf.neg', [status(esa)], [t10_connsp_2])).
% 0.35/0.52  thf('0', plain,
% 0.35/0.52      ((~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.35/0.52        | ~ (m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.52             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('1', plain,
% 0.35/0.52      (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.35/0.52       ~
% 0.35/0.52       ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.52         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.35/0.52      inference('split', [status(esa)], ['0'])).
% 0.35/0.52  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf(redefinition_k6_domain_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.35/0.52       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.35/0.52  thf('3', plain,
% 0.35/0.52      (![X36 : $i, X37 : $i]:
% 0.35/0.52         ((v1_xboole_0 @ X36)
% 0.35/0.52          | ~ (m1_subset_1 @ X37 @ X36)
% 0.35/0.52          | ((k6_domain_1 @ X36 @ X37) = (k1_tarski @ X37)))),
% 0.35/0.52      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.35/0.52  thf('4', plain,
% 0.35/0.52      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.35/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.35/0.52  thf('5', plain,
% 0.35/0.52      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.35/0.52        | (m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.52           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('6', plain,
% 0.35/0.52      (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.52         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.35/0.52         <= (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.52               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.52      inference('split', [status(esa)], ['5'])).
% 0.35/0.52  thf('7', plain,
% 0.35/0.52      ((((m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.35/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.35/0.52         <= (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.52               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.52      inference('sup+', [status(thm)], ['4', '6'])).
% 0.35/0.52  thf('8', plain,
% 0.35/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('9', plain,
% 0.35/0.52      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.35/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.35/0.52  thf('10', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf(dt_k6_domain_1, axiom,
% 0.35/0.52    (![A:$i,B:$i]:
% 0.35/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.35/0.52       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.35/0.52  thf('11', plain,
% 0.35/0.52      (![X34 : $i, X35 : $i]:
% 0.35/0.52         ((v1_xboole_0 @ X34)
% 0.35/0.52          | ~ (m1_subset_1 @ X35 @ X34)
% 0.35/0.52          | (m1_subset_1 @ (k6_domain_1 @ X34 @ X35) @ (k1_zfmisc_1 @ X34)))),
% 0.35/0.52      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.35/0.52  thf('12', plain,
% 0.35/0.52      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.35/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.35/0.52  thf('13', plain,
% 0.35/0.52      (((m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.35/0.52         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.52      inference('sup+', [status(thm)], ['9', '12'])).
% 0.35/0.52  thf('14', plain,
% 0.35/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.52        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.35/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.52      inference('simplify', [status(thm)], ['13'])).
% 0.35/0.52  thf(d2_connsp_2, axiom,
% 0.35/0.52    (![A:$i]:
% 0.35/0.52     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.52       ( ![B:$i]:
% 0.35/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.52           ( ![C:$i]:
% 0.35/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.52               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.35/0.52                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.35/0.52  thf('15', plain,
% 0.35/0.52      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.35/0.52         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.35/0.52          | ~ (m2_connsp_2 @ X43 @ X42 @ X41)
% 0.35/0.52          | (r1_tarski @ X41 @ (k1_tops_1 @ X42 @ X43))
% 0.35/0.52          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.35/0.52          | ~ (l1_pre_topc @ X42)
% 0.35/0.52          | ~ (v2_pre_topc @ X42))),
% 0.35/0.52      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.35/0.52  thf('16', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.35/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.35/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.52          | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.35/0.52          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.35/0.52  thf('17', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('19', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.52          | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.35/0.52          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.35/0.52      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.35/0.52  thf('20', plain,
% 0.35/0.52      ((~ (m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.35/0.52        | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['8', '19'])).
% 0.35/0.52  thf('21', plain,
% 0.35/0.52      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.52         | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.35/0.52         <= (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.52               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.52      inference('sup-', [status(thm)], ['7', '20'])).
% 0.35/0.52  thf('22', plain,
% 0.35/0.52      ((((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.35/0.52         <= (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.52               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.52      inference('simplify', [status(thm)], ['21'])).
% 0.35/0.52  thf(t69_enumset1, axiom,
% 0.35/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.35/0.52  thf('23', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.52  thf(t38_zfmisc_1, axiom,
% 0.35/0.52    (![A:$i,B:$i,C:$i]:
% 0.35/0.52     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.35/0.52       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.35/0.52  thf('24', plain,
% 0.35/0.52      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.35/0.52         ((r2_hidden @ X28 @ X29)
% 0.35/0.52          | ~ (r1_tarski @ (k2_tarski @ X28 @ X30) @ X29))),
% 0.35/0.52      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.35/0.52  thf('25', plain,
% 0.35/0.52      (![X0 : $i, X1 : $i]:
% 0.35/0.52         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.35/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.35/0.52  thf('26', plain,
% 0.35/0.52      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.52         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.35/0.52         <= (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.52               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.52      inference('sup-', [status(thm)], ['22', '25'])).
% 0.35/0.52  thf('27', plain,
% 0.35/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf(d1_connsp_2, axiom,
% 0.35/0.52    (![A:$i]:
% 0.35/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.35/0.52       ( ![B:$i]:
% 0.35/0.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.35/0.52           ( ![C:$i]:
% 0.35/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.35/0.52               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.35/0.52                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.35/0.52  thf('28', plain,
% 0.35/0.52      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.35/0.52         (~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X39))
% 0.35/0.52          | ~ (r2_hidden @ X38 @ (k1_tops_1 @ X39 @ X40))
% 0.35/0.52          | (m1_connsp_2 @ X40 @ X39 @ X38)
% 0.35/0.52          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.35/0.52          | ~ (l1_pre_topc @ X39)
% 0.35/0.52          | ~ (v2_pre_topc @ X39)
% 0.35/0.52          | (v2_struct_0 @ X39))),
% 0.35/0.52      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.35/0.52  thf('29', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         ((v2_struct_0 @ sk_A)
% 0.35/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.35/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.35/0.52          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.35/0.52          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.35/0.52  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('32', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         ((v2_struct_0 @ sk_A)
% 0.35/0.52          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.35/0.52          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.52      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.35/0.52  thf('33', plain,
% 0.35/0.52      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.52         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.35/0.52         | (m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.35/0.52         | (v2_struct_0 @ sk_A)))
% 0.35/0.52         <= (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.52               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.52      inference('sup-', [status(thm)], ['26', '32'])).
% 0.35/0.52  thf('34', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('35', plain,
% 0.35/0.52      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.52         | (m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.35/0.52         | (v2_struct_0 @ sk_A)))
% 0.35/0.52         <= (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.52               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.52      inference('demod', [status(thm)], ['33', '34'])).
% 0.35/0.52  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('37', plain,
% 0.35/0.52      ((((m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.35/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.35/0.52         <= (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.52               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.52      inference('clc', [status(thm)], ['35', '36'])).
% 0.35/0.52  thf('38', plain,
% 0.35/0.52      ((~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 0.35/0.52         <= (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.52      inference('split', [status(esa)], ['0'])).
% 0.35/0.52  thf('39', plain,
% 0.35/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.35/0.52         <= (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) & 
% 0.35/0.52             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.52               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.35/0.52  thf(fc2_struct_0, axiom,
% 0.35/0.52    (![A:$i]:
% 0.35/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.35/0.52       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.35/0.52  thf('40', plain,
% 0.35/0.52      (![X33 : $i]:
% 0.35/0.52         (~ (v1_xboole_0 @ (u1_struct_0 @ X33))
% 0.35/0.52          | ~ (l1_struct_0 @ X33)
% 0.35/0.52          | (v2_struct_0 @ X33))),
% 0.35/0.52      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.35/0.52  thf('41', plain,
% 0.35/0.52      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.35/0.52         <= (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) & 
% 0.35/0.52             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.52               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.52      inference('sup-', [status(thm)], ['39', '40'])).
% 0.35/0.52  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf(dt_l1_pre_topc, axiom,
% 0.35/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.35/0.52  thf('43', plain,
% 0.35/0.52      (![X32 : $i]: ((l1_struct_0 @ X32) | ~ (l1_pre_topc @ X32))),
% 0.35/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.35/0.52  thf('44', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.52      inference('sup-', [status(thm)], ['42', '43'])).
% 0.35/0.52  thf('45', plain,
% 0.35/0.52      (((v2_struct_0 @ sk_A))
% 0.35/0.52         <= (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) & 
% 0.35/0.52             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.52               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.52      inference('demod', [status(thm)], ['41', '44'])).
% 0.35/0.52  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('47', plain,
% 0.35/0.52      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.35/0.52       ~
% 0.35/0.52       ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.52         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.35/0.52  thf('48', plain,
% 0.35/0.52      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.35/0.52       ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.52         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.35/0.52      inference('split', [status(esa)], ['5'])).
% 0.35/0.52  thf('49', plain,
% 0.35/0.52      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 0.35/0.52         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.52      inference('split', [status(esa)], ['5'])).
% 0.35/0.52  thf('50', plain,
% 0.35/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('51', plain,
% 0.35/0.52      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.35/0.52         (~ (m1_subset_1 @ X38 @ (u1_struct_0 @ X39))
% 0.35/0.52          | ~ (m1_connsp_2 @ X40 @ X39 @ X38)
% 0.35/0.52          | (r2_hidden @ X38 @ (k1_tops_1 @ X39 @ X40))
% 0.35/0.52          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.35/0.52          | ~ (l1_pre_topc @ X39)
% 0.35/0.52          | ~ (v2_pre_topc @ X39)
% 0.35/0.52          | (v2_struct_0 @ X39))),
% 0.35/0.52      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.35/0.52  thf('52', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         ((v2_struct_0 @ sk_A)
% 0.35/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.35/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.35/0.52          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.52          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.35/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['50', '51'])).
% 0.35/0.52  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('55', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         ((v2_struct_0 @ sk_A)
% 0.35/0.52          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.52          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.35/0.52          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.52      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.35/0.52  thf('56', plain,
% 0.35/0.52      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.35/0.52         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.52         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['49', '55'])).
% 0.35/0.52  thf('57', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('58', plain,
% 0.35/0.52      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A)))
% 0.35/0.52         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.52      inference('demod', [status(thm)], ['56', '57'])).
% 0.35/0.52  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('60', plain,
% 0.35/0.52      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.35/0.52         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.52      inference('clc', [status(thm)], ['58', '59'])).
% 0.35/0.52  thf('61', plain,
% 0.35/0.52      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.35/0.52         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.52      inference('clc', [status(thm)], ['58', '59'])).
% 0.35/0.52  thf('62', plain,
% 0.35/0.52      (![X28 : $i, X30 : $i, X31 : $i]:
% 0.35/0.52         ((r1_tarski @ (k2_tarski @ X28 @ X30) @ X31)
% 0.35/0.52          | ~ (r2_hidden @ X30 @ X31)
% 0.35/0.52          | ~ (r2_hidden @ X28 @ X31))),
% 0.35/0.52      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.35/0.52  thf('63', plain,
% 0.35/0.52      ((![X0 : $i]:
% 0.35/0.52          (~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.35/0.52           | (r1_tarski @ (k2_tarski @ X0 @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.35/0.52         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['61', '62'])).
% 0.35/0.52  thf('64', plain,
% 0.35/0.52      (((r1_tarski @ (k2_tarski @ sk_B @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.35/0.52         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['60', '63'])).
% 0.35/0.52  thf('65', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.35/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.52  thf('66', plain,
% 0.35/0.52      (((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.35/0.52         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.52      inference('demod', [status(thm)], ['64', '65'])).
% 0.35/0.52  thf('67', plain,
% 0.35/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.52        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.35/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.35/0.52      inference('simplify', [status(thm)], ['13'])).
% 0.35/0.52  thf('68', plain,
% 0.35/0.52      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.35/0.52         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.35/0.52          | ~ (r1_tarski @ X41 @ (k1_tops_1 @ X42 @ X43))
% 0.35/0.52          | (m2_connsp_2 @ X43 @ X42 @ X41)
% 0.35/0.52          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.35/0.52          | ~ (l1_pre_topc @ X42)
% 0.35/0.52          | ~ (v2_pre_topc @ X42))),
% 0.35/0.52      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.35/0.52  thf('69', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.52          | ~ (v2_pre_topc @ sk_A)
% 0.35/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.35/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.52          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.35/0.52          | ~ (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['67', '68'])).
% 0.35/0.52  thf('70', plain, ((v2_pre_topc @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('72', plain,
% 0.35/0.52      (![X0 : $i]:
% 0.35/0.52         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.52          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.35/0.52          | ~ (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.35/0.52      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.35/0.52  thf('73', plain,
% 0.35/0.52      ((((m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.35/0.52         | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.35/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.35/0.52         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['66', '72'])).
% 0.35/0.52  thf('74', plain,
% 0.35/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.52  thf('75', plain,
% 0.35/0.52      ((((m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.35/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.35/0.52         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.52      inference('demod', [status(thm)], ['73', '74'])).
% 0.35/0.52  thf('76', plain,
% 0.35/0.52      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.35/0.52        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.35/0.52  thf('77', plain,
% 0.35/0.52      ((~ (m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.52           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.35/0.52         <= (~
% 0.35/0.52             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.52               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.52      inference('split', [status(esa)], ['0'])).
% 0.35/0.52  thf('78', plain,
% 0.35/0.52      (((~ (m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.35/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.35/0.52         <= (~
% 0.35/0.52             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.52               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.35/0.52      inference('sup-', [status(thm)], ['76', '77'])).
% 0.35/0.52  thf('79', plain,
% 0.35/0.52      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.35/0.52         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.35/0.52         <= (~
% 0.35/0.52             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.52               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.35/0.52             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.52      inference('sup-', [status(thm)], ['75', '78'])).
% 0.35/0.52  thf('80', plain,
% 0.35/0.52      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.35/0.52         <= (~
% 0.35/0.52             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.52               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.35/0.52             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.52      inference('simplify', [status(thm)], ['79'])).
% 0.35/0.53  thf('81', plain,
% 0.35/0.53      (![X33 : $i]:
% 0.35/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X33))
% 0.35/0.53          | ~ (l1_struct_0 @ X33)
% 0.35/0.53          | (v2_struct_0 @ X33))),
% 0.35/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.35/0.53  thf('82', plain,
% 0.35/0.53      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.35/0.53         <= (~
% 0.35/0.53             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.35/0.53             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['80', '81'])).
% 0.35/0.53  thf('83', plain, ((l1_struct_0 @ sk_A)),
% 0.35/0.53      inference('sup-', [status(thm)], ['42', '43'])).
% 0.35/0.53  thf('84', plain,
% 0.35/0.53      (((v2_struct_0 @ sk_A))
% 0.35/0.53         <= (~
% 0.35/0.53             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.35/0.53             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.35/0.53      inference('demod', [status(thm)], ['82', '83'])).
% 0.35/0.53  thf('85', plain, (~ (v2_struct_0 @ sk_A)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('86', plain,
% 0.35/0.53      (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.35/0.53       ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.35/0.53         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['84', '85'])).
% 0.35/0.53  thf('87', plain, ($false),
% 0.35/0.53      inference('sat_resolution*', [status(thm)], ['1', '47', '48', '86'])).
% 0.35/0.53  
% 0.35/0.53  % SZS output end Refutation
% 0.35/0.53  
% 0.37/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
