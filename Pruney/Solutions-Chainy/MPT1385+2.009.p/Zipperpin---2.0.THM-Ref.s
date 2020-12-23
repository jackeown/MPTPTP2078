%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ONSLMfdkqg

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:59 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 352 expanded)
%              Number of leaves         :   28 ( 108 expanded)
%              Depth                    :   28
%              Number of atoms          :  999 (5260 expanded)
%              Number of equality atoms :    8 (  24 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ X22 )
      | ( ( k6_domain_1 @ X22 @ X23 )
        = ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('4',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

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

thf('10',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m2_connsp_2 @ X29 @ X28 @ X27 )
      | ( r1_tarski @ X27 @ ( k1_tops_1 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('17',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 )
    | ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
   <= ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['16','18'])).

thf('20',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['17'])).

thf('23',plain,(
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

thf('24',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ~ ( m1_connsp_2 @ X26 @ X25 @ X24 )
      | ( r2_hidden @ X24 @ ( k1_tops_1 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['31','32'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X6 @ X8 ) @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
        | ( r1_tarski @ ( k2_tarski @ X0 @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_B_1 @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('38',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('39',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('41',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( r1_tarski @ X27 @ ( k1_tops_1 @ X28 @ X29 ) )
      | ( m2_connsp_2 @ X29 @ X28 @ X27 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('50',plain,
    ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
   <= ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['20'])).

thf('51',plain,
    ( ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('54',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('55',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('57',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('58',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['17'])).

thf('63',plain,(
    m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['21','61','62'])).

thf('64',plain,
    ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['19','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['15','64'])).

thf('66',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('67',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_tarski @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X25 ) )
      | ~ ( r2_hidden @ X24 @ ( k1_tops_1 @ X25 @ X26 ) )
      | ( m1_connsp_2 @ X26 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 )
   <= ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['20'])).

thf('80',plain,(
    ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['21','61'])).

thf('81',plain,(
    ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['78','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['56','57'])).

thf('88',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['0','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ONSLMfdkqg
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:01:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.55/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.72  % Solved by: fo/fo7.sh
% 0.55/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.72  % done 658 iterations in 0.263s
% 0.55/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.72  % SZS output start Refutation
% 0.55/0.72  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.55/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.72  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.55/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.55/0.72  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.55/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.55/0.72  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.55/0.72  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.55/0.72  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.55/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.72  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.55/0.72  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.55/0.72  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.55/0.72  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.55/0.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.55/0.72  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.55/0.72  thf(t10_connsp_2, conjecture,
% 0.55/0.72    (![A:$i]:
% 0.55/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.72       ( ![B:$i]:
% 0.55/0.72         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.55/0.72           ( ![C:$i]:
% 0.55/0.72             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.72               ( ( m2_connsp_2 @
% 0.55/0.72                   C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.55/0.72                 ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ))).
% 0.55/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.72    (~( ![A:$i]:
% 0.55/0.72        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.55/0.72            ( l1_pre_topc @ A ) ) =>
% 0.55/0.72          ( ![B:$i]:
% 0.55/0.72            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.55/0.72              ( ![C:$i]:
% 0.55/0.72                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.72                  ( ( m2_connsp_2 @
% 0.55/0.72                      C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.55/0.72                    ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ) )),
% 0.55/0.72    inference('cnf.neg', [status(esa)], [t10_connsp_2])).
% 0.55/0.72  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('1', plain,
% 0.55/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('2', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf(redefinition_k6_domain_1, axiom,
% 0.55/0.72    (![A:$i,B:$i]:
% 0.55/0.72     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.55/0.72       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.55/0.72  thf('3', plain,
% 0.55/0.72      (![X22 : $i, X23 : $i]:
% 0.55/0.72         ((v1_xboole_0 @ X22)
% 0.55/0.72          | ~ (m1_subset_1 @ X23 @ X22)
% 0.55/0.72          | ((k6_domain_1 @ X22 @ X23) = (k1_tarski @ X23)))),
% 0.55/0.72      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.55/0.72  thf('4', plain,
% 0.55/0.72      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.55/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.55/0.72  thf('5', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf(dt_k6_domain_1, axiom,
% 0.55/0.72    (![A:$i,B:$i]:
% 0.55/0.72     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.55/0.72       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.55/0.72  thf('6', plain,
% 0.55/0.72      (![X20 : $i, X21 : $i]:
% 0.55/0.72         ((v1_xboole_0 @ X20)
% 0.55/0.72          | ~ (m1_subset_1 @ X21 @ X20)
% 0.55/0.72          | (m1_subset_1 @ (k6_domain_1 @ X20 @ X21) @ (k1_zfmisc_1 @ X20)))),
% 0.55/0.72      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.55/0.72  thf('7', plain,
% 0.55/0.72      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.55/0.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['5', '6'])).
% 0.55/0.72  thf('8', plain,
% 0.55/0.72      (((m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.55/0.72         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.72      inference('sup+', [status(thm)], ['4', '7'])).
% 0.55/0.72  thf('9', plain,
% 0.55/0.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.72        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.55/0.72           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.72      inference('simplify', [status(thm)], ['8'])).
% 0.55/0.72  thf(d2_connsp_2, axiom,
% 0.55/0.72    (![A:$i]:
% 0.55/0.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.72       ( ![B:$i]:
% 0.55/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.72           ( ![C:$i]:
% 0.55/0.72             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.72               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.55/0.72                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.55/0.72  thf('10', plain,
% 0.55/0.72      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.55/0.72         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.55/0.72          | ~ (m2_connsp_2 @ X29 @ X28 @ X27)
% 0.55/0.72          | (r1_tarski @ X27 @ (k1_tops_1 @ X28 @ X29))
% 0.55/0.72          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.55/0.72          | ~ (l1_pre_topc @ X28)
% 0.55/0.72          | ~ (v2_pre_topc @ X28))),
% 0.55/0.72      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.55/0.72  thf('11', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.72          | ~ (v2_pre_topc @ sk_A)
% 0.55/0.72          | ~ (l1_pre_topc @ sk_A)
% 0.55/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.72          | (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ X0))
% 0.55/0.72          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['9', '10'])).
% 0.55/0.72  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('14', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.72          | (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ X0))
% 0.55/0.72          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B_1)))),
% 0.55/0.72      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.55/0.72  thf('15', plain,
% 0.55/0.72      ((~ (m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B_1))
% 0.55/0.72        | (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_C))
% 0.55/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['1', '14'])).
% 0.55/0.72  thf('16', plain,
% 0.55/0.72      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.55/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.55/0.72  thf('17', plain,
% 0.55/0.72      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)
% 0.55/0.72        | (m2_connsp_2 @ sk_C @ sk_A @ 
% 0.55/0.72           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('18', plain,
% 0.55/0.72      (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.55/0.72         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.55/0.72         <= (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.55/0.72               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.55/0.72      inference('split', [status(esa)], ['17'])).
% 0.55/0.72  thf('19', plain,
% 0.55/0.72      ((((m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B_1))
% 0.55/0.72         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.55/0.72         <= (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.55/0.72               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.55/0.72      inference('sup+', [status(thm)], ['16', '18'])).
% 0.55/0.72  thf('20', plain,
% 0.55/0.72      ((~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)
% 0.55/0.72        | ~ (m2_connsp_2 @ sk_C @ sk_A @ 
% 0.55/0.72             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('21', plain,
% 0.55/0.72      (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)) | 
% 0.55/0.72       ~
% 0.55/0.72       ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.55/0.72         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.55/0.72      inference('split', [status(esa)], ['20'])).
% 0.55/0.72  thf('22', plain,
% 0.55/0.72      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1))
% 0.55/0.72         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)))),
% 0.55/0.72      inference('split', [status(esa)], ['17'])).
% 0.55/0.72  thf('23', plain,
% 0.55/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf(d1_connsp_2, axiom,
% 0.55/0.72    (![A:$i]:
% 0.55/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.55/0.72       ( ![B:$i]:
% 0.55/0.72         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.55/0.72           ( ![C:$i]:
% 0.55/0.72             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.72               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.55/0.72                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.55/0.72  thf('24', plain,
% 0.55/0.72      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.55/0.72         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.55/0.72          | ~ (m1_connsp_2 @ X26 @ X25 @ X24)
% 0.55/0.72          | (r2_hidden @ X24 @ (k1_tops_1 @ X25 @ X26))
% 0.55/0.72          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.55/0.72          | ~ (l1_pre_topc @ X25)
% 0.55/0.72          | ~ (v2_pre_topc @ X25)
% 0.55/0.72          | (v2_struct_0 @ X25))),
% 0.55/0.72      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.55/0.72  thf('25', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         ((v2_struct_0 @ sk_A)
% 0.55/0.72          | ~ (v2_pre_topc @ sk_A)
% 0.55/0.72          | ~ (l1_pre_topc @ sk_A)
% 0.55/0.72          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.55/0.72          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.55/0.72          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['23', '24'])).
% 0.55/0.72  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('28', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         ((v2_struct_0 @ sk_A)
% 0.55/0.72          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.55/0.72          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.55/0.72          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.72      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.55/0.72  thf('29', plain,
% 0.55/0.72      (((~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.55/0.72         | (r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.55/0.72         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['22', '28'])).
% 0.55/0.72  thf('30', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('31', plain,
% 0.55/0.72      ((((r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.55/0.72         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)))),
% 0.55/0.72      inference('demod', [status(thm)], ['29', '30'])).
% 0.55/0.72  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('33', plain,
% 0.55/0.72      (((r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.55/0.72         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)))),
% 0.55/0.72      inference('clc', [status(thm)], ['31', '32'])).
% 0.55/0.72  thf('34', plain,
% 0.55/0.72      (((r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.55/0.72         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)))),
% 0.55/0.72      inference('clc', [status(thm)], ['31', '32'])).
% 0.55/0.72  thf(t38_zfmisc_1, axiom,
% 0.55/0.72    (![A:$i,B:$i,C:$i]:
% 0.55/0.72     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.55/0.72       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.55/0.72  thf('35', plain,
% 0.55/0.72      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.55/0.72         ((r1_tarski @ (k2_tarski @ X6 @ X8) @ X9)
% 0.55/0.72          | ~ (r2_hidden @ X8 @ X9)
% 0.55/0.72          | ~ (r2_hidden @ X6 @ X9))),
% 0.55/0.72      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.55/0.72  thf('36', plain,
% 0.55/0.72      ((![X0 : $i]:
% 0.55/0.72          (~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.55/0.72           | (r1_tarski @ (k2_tarski @ X0 @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_C))))
% 0.55/0.72         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['34', '35'])).
% 0.55/0.72  thf('37', plain,
% 0.55/0.72      (((r1_tarski @ (k2_tarski @ sk_B_1 @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.55/0.72         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['33', '36'])).
% 0.55/0.72  thf(t69_enumset1, axiom,
% 0.55/0.72    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.55/0.72  thf('38', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.55/0.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.55/0.72  thf('39', plain,
% 0.55/0.72      (((r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.55/0.72         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)))),
% 0.55/0.72      inference('demod', [status(thm)], ['37', '38'])).
% 0.55/0.72  thf('40', plain,
% 0.55/0.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.72        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.55/0.72           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.55/0.72      inference('simplify', [status(thm)], ['8'])).
% 0.55/0.72  thf('41', plain,
% 0.55/0.72      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.55/0.72         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.55/0.72          | ~ (r1_tarski @ X27 @ (k1_tops_1 @ X28 @ X29))
% 0.55/0.72          | (m2_connsp_2 @ X29 @ X28 @ X27)
% 0.55/0.72          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.55/0.72          | ~ (l1_pre_topc @ X28)
% 0.55/0.72          | ~ (v2_pre_topc @ X28))),
% 0.55/0.72      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.55/0.72  thf('42', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.72          | ~ (v2_pre_topc @ sk_A)
% 0.55/0.72          | ~ (l1_pre_topc @ sk_A)
% 0.55/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.72          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.55/0.72          | ~ (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['40', '41'])).
% 0.55/0.72  thf('43', plain, ((v2_pre_topc @ sk_A)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('45', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.72          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.55/0.72          | ~ (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.55/0.72      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.55/0.72  thf('46', plain,
% 0.55/0.72      ((((m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B_1))
% 0.55/0.72         | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.55/0.72         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.55/0.72         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['39', '45'])).
% 0.55/0.72  thf('47', plain,
% 0.55/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('48', plain,
% 0.55/0.72      ((((m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B_1))
% 0.55/0.72         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.55/0.72         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)))),
% 0.55/0.72      inference('demod', [status(thm)], ['46', '47'])).
% 0.55/0.72  thf('49', plain,
% 0.55/0.72      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.55/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.55/0.72  thf('50', plain,
% 0.55/0.72      ((~ (m2_connsp_2 @ sk_C @ sk_A @ 
% 0.55/0.72           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.55/0.72         <= (~
% 0.55/0.72             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.55/0.72               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.55/0.72      inference('split', [status(esa)], ['20'])).
% 0.55/0.72  thf('51', plain,
% 0.55/0.72      (((~ (m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B_1))
% 0.55/0.72         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.55/0.72         <= (~
% 0.55/0.72             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.55/0.72               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.55/0.72      inference('sup-', [status(thm)], ['49', '50'])).
% 0.55/0.72  thf('52', plain,
% 0.55/0.72      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.72         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.55/0.72         <= (~
% 0.55/0.72             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.55/0.72               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) & 
% 0.55/0.72             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['48', '51'])).
% 0.55/0.72  thf('53', plain,
% 0.55/0.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.55/0.72         <= (~
% 0.55/0.72             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.55/0.72               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) & 
% 0.55/0.72             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)))),
% 0.55/0.72      inference('simplify', [status(thm)], ['52'])).
% 0.55/0.72  thf(fc2_struct_0, axiom,
% 0.55/0.72    (![A:$i]:
% 0.55/0.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.55/0.72       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.55/0.72  thf('54', plain,
% 0.55/0.72      (![X19 : $i]:
% 0.55/0.72         (~ (v1_xboole_0 @ (u1_struct_0 @ X19))
% 0.55/0.72          | ~ (l1_struct_0 @ X19)
% 0.55/0.72          | (v2_struct_0 @ X19))),
% 0.55/0.72      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.55/0.72  thf('55', plain,
% 0.55/0.72      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.55/0.72         <= (~
% 0.55/0.72             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.55/0.72               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) & 
% 0.55/0.72             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['53', '54'])).
% 0.55/0.72  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf(dt_l1_pre_topc, axiom,
% 0.55/0.72    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.55/0.72  thf('57', plain,
% 0.55/0.72      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.55/0.72      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.55/0.72  thf('58', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.72      inference('sup-', [status(thm)], ['56', '57'])).
% 0.55/0.72  thf('59', plain,
% 0.55/0.72      (((v2_struct_0 @ sk_A))
% 0.55/0.72         <= (~
% 0.55/0.72             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.55/0.72               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) & 
% 0.55/0.72             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)))),
% 0.55/0.72      inference('demod', [status(thm)], ['55', '58'])).
% 0.55/0.72  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('61', plain,
% 0.55/0.72      (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.55/0.72         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) | 
% 0.55/0.72       ~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1))),
% 0.55/0.72      inference('sup-', [status(thm)], ['59', '60'])).
% 0.55/0.72  thf('62', plain,
% 0.55/0.72      (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.55/0.72         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1))) | 
% 0.55/0.72       ((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1))),
% 0.55/0.72      inference('split', [status(esa)], ['17'])).
% 0.55/0.72  thf('63', plain,
% 0.55/0.72      (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.55/0.72         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.55/0.72      inference('sat_resolution*', [status(thm)], ['21', '61', '62'])).
% 0.55/0.72  thf('64', plain,
% 0.55/0.72      (((m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B_1))
% 0.55/0.72        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.72      inference('simpl_trail', [status(thm)], ['19', '63'])).
% 0.55/0.72  thf('65', plain,
% 0.55/0.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.72        | (r1_tarski @ (k1_tarski @ sk_B_1) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.55/0.72      inference('clc', [status(thm)], ['15', '64'])).
% 0.55/0.72  thf('66', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.55/0.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.55/0.72  thf('67', plain,
% 0.55/0.72      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.55/0.72         ((r2_hidden @ X6 @ X7) | ~ (r1_tarski @ (k2_tarski @ X6 @ X8) @ X7))),
% 0.55/0.72      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.55/0.72  thf('68', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i]:
% 0.55/0.72         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.55/0.72      inference('sup-', [status(thm)], ['66', '67'])).
% 0.55/0.72  thf('69', plain,
% 0.55/0.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.72        | (r2_hidden @ sk_B_1 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['65', '68'])).
% 0.55/0.72  thf('70', plain,
% 0.55/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('71', plain,
% 0.55/0.72      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.55/0.72         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X25))
% 0.55/0.72          | ~ (r2_hidden @ X24 @ (k1_tops_1 @ X25 @ X26))
% 0.55/0.72          | (m1_connsp_2 @ X26 @ X25 @ X24)
% 0.55/0.72          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.55/0.72          | ~ (l1_pre_topc @ X25)
% 0.55/0.72          | ~ (v2_pre_topc @ X25)
% 0.55/0.72          | (v2_struct_0 @ X25))),
% 0.55/0.72      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.55/0.72  thf('72', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         ((v2_struct_0 @ sk_A)
% 0.55/0.72          | ~ (v2_pre_topc @ sk_A)
% 0.55/0.72          | ~ (l1_pre_topc @ sk_A)
% 0.55/0.72          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.55/0.72          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.55/0.72          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['70', '71'])).
% 0.55/0.72  thf('73', plain, ((v2_pre_topc @ sk_A)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('75', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         ((v2_struct_0 @ sk_A)
% 0.55/0.72          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.55/0.72          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.55/0.72          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.72      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.55/0.72  thf('76', plain,
% 0.55/0.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.72        | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.55/0.72        | (m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)
% 0.55/0.72        | (v2_struct_0 @ sk_A))),
% 0.55/0.72      inference('sup-', [status(thm)], ['69', '75'])).
% 0.55/0.72  thf('77', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('78', plain,
% 0.55/0.72      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.55/0.72        | (m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)
% 0.55/0.72        | (v2_struct_0 @ sk_A))),
% 0.55/0.72      inference('demod', [status(thm)], ['76', '77'])).
% 0.55/0.72  thf('79', plain,
% 0.55/0.72      ((~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B_1))
% 0.55/0.72         <= (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)))),
% 0.55/0.72      inference('split', [status(esa)], ['20'])).
% 0.55/0.72  thf('80', plain, (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B_1))),
% 0.55/0.72      inference('sat_resolution*', [status(thm)], ['21', '61'])).
% 0.55/0.72  thf('81', plain, (~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.55/0.72      inference('simpl_trail', [status(thm)], ['79', '80'])).
% 0.55/0.72  thf('82', plain,
% 0.55/0.72      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.55/0.72      inference('clc', [status(thm)], ['78', '81'])).
% 0.55/0.72  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('84', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.55/0.72      inference('clc', [status(thm)], ['82', '83'])).
% 0.55/0.72  thf('85', plain,
% 0.55/0.72      (![X19 : $i]:
% 0.55/0.72         (~ (v1_xboole_0 @ (u1_struct_0 @ X19))
% 0.55/0.72          | ~ (l1_struct_0 @ X19)
% 0.55/0.72          | (v2_struct_0 @ X19))),
% 0.55/0.72      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.55/0.72  thf('86', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.55/0.72      inference('sup-', [status(thm)], ['84', '85'])).
% 0.55/0.72  thf('87', plain, ((l1_struct_0 @ sk_A)),
% 0.55/0.72      inference('sup-', [status(thm)], ['56', '57'])).
% 0.55/0.72  thf('88', plain, ((v2_struct_0 @ sk_A)),
% 0.55/0.72      inference('demod', [status(thm)], ['86', '87'])).
% 0.55/0.72  thf('89', plain, ($false), inference('demod', [status(thm)], ['0', '88'])).
% 0.55/0.72  
% 0.55/0.72  % SZS output end Refutation
% 0.55/0.72  
% 0.55/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
