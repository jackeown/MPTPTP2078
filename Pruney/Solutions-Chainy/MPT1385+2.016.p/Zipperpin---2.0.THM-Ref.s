%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7vumRFczl7

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:01 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 288 expanded)
%              Number of leaves         :   26 (  90 expanded)
%              Depth                    :   26
%              Number of atoms          :  929 (4216 expanded)
%              Number of equality atoms :    5 (  18 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ X7 )
      | ( ( k6_domain_1 @ X7 @ X8 )
        = ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('4',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ X5 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m2_connsp_2 @ X14 @ X13 @ X12 )
      | ( r1_tarski @ X12 @ ( k1_tops_1 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
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
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('17',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['16','18'])).

thf('20',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_connsp_2 @ X11 @ X10 @ X9 )
      | ( r2_hidden @ X9 @ ( k1_tops_1 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
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
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['31','32'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('34',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('35',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('37',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r1_tarski @ X12 @ ( k1_tops_1 @ X13 @ X14 ) )
      | ( m2_connsp_2 @ X14 @ X13 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('46',plain,
    ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['20'])).

thf('47',plain,
    ( ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('50',plain,(
    ! [X4: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('51',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('53',plain,(
    ! [X3: $i] :
      ( ( l1_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('54',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf('59',plain,(
    m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['21','57','58'])).

thf('60',plain,
    ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['19','59'])).

thf('61',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['15','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r2_hidden @ X9 @ ( k1_tops_1 @ X10 @ X11 ) )
      | ( m1_connsp_2 @ X11 @ X10 @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['20'])).

thf('74',plain,(
    ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['21','57'])).

thf('75',plain,(
    ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['72','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X4: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('82',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['0','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7vumRFczl7
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:41:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 83 iterations in 0.052s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.50  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.19/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.50  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.19/0.50  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.50  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.19/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.50  thf(t10_connsp_2, conjecture,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.50           ( ![C:$i]:
% 0.19/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.50               ( ( m2_connsp_2 @
% 0.19/0.50                   C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.19/0.50                 ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i]:
% 0.19/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.50            ( l1_pre_topc @ A ) ) =>
% 0.19/0.50          ( ![B:$i]:
% 0.19/0.50            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.50              ( ![C:$i]:
% 0.19/0.50                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.50                  ( ( m2_connsp_2 @
% 0.19/0.50                      C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.19/0.50                    ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t10_connsp_2])).
% 0.19/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('1', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(redefinition_k6_domain_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.19/0.50       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      (![X7 : $i, X8 : $i]:
% 0.19/0.50         ((v1_xboole_0 @ X7)
% 0.19/0.50          | ~ (m1_subset_1 @ X8 @ X7)
% 0.19/0.50          | ((k6_domain_1 @ X7 @ X8) = (k1_tarski @ X8)))),
% 0.19/0.50      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.19/0.50  thf('4', plain,
% 0.19/0.50      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.50  thf('5', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(dt_k6_domain_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.19/0.50       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      (![X5 : $i, X6 : $i]:
% 0.19/0.50         ((v1_xboole_0 @ X5)
% 0.19/0.50          | ~ (m1_subset_1 @ X6 @ X5)
% 0.19/0.50          | (m1_subset_1 @ (k6_domain_1 @ X5 @ X6) @ (k1_zfmisc_1 @ X5)))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      (((m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.19/0.50         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['4', '7'])).
% 0.19/0.50  thf('9', plain,
% 0.19/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.19/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.19/0.50  thf(d2_connsp_2, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.50           ( ![C:$i]:
% 0.19/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.50               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.19/0.50                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.19/0.50  thf('10', plain,
% 0.19/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.19/0.50          | ~ (m2_connsp_2 @ X14 @ X13 @ X12)
% 0.19/0.50          | (r1_tarski @ X12 @ (k1_tops_1 @ X13 @ X14))
% 0.19/0.50          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.19/0.50          | ~ (l1_pre_topc @ X13)
% 0.19/0.50          | ~ (v2_pre_topc @ X13))),
% 0.19/0.50      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.19/0.50  thf('11', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.50          | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.19/0.50          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.50  thf('12', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('14', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.50          | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.19/0.50          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.19/0.50      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      ((~ (m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.19/0.50        | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['1', '14'])).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.50  thf('17', plain,
% 0.19/0.50      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.19/0.50        | (m2_connsp_2 @ sk_C @ sk_A @ 
% 0.19/0.50           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('18', plain,
% 0.19/0.50      (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.19/0.50         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.19/0.50         <= (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.19/0.50               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.19/0.50      inference('split', [status(esa)], ['17'])).
% 0.19/0.50  thf('19', plain,
% 0.19/0.50      ((((m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.19/0.50         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.19/0.50         <= (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.19/0.50               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.19/0.50      inference('sup+', [status(thm)], ['16', '18'])).
% 0.19/0.50  thf('20', plain,
% 0.19/0.50      ((~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.19/0.50        | ~ (m2_connsp_2 @ sk_C @ sk_A @ 
% 0.19/0.50             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.19/0.50       ~
% 0.19/0.50       ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.19/0.50         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.50      inference('split', [status(esa)], ['20'])).
% 0.19/0.50  thf('22', plain,
% 0.19/0.50      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 0.19/0.50         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.50      inference('split', [status(esa)], ['17'])).
% 0.19/0.50  thf('23', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(d1_connsp_2, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.50           ( ![C:$i]:
% 0.19/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.50               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.19/0.50                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.19/0.50  thf('24', plain,
% 0.19/0.50      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.19/0.50          | ~ (m1_connsp_2 @ X11 @ X10 @ X9)
% 0.19/0.50          | (r2_hidden @ X9 @ (k1_tops_1 @ X10 @ X11))
% 0.19/0.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.19/0.50          | ~ (l1_pre_topc @ X10)
% 0.19/0.50          | ~ (v2_pre_topc @ X10)
% 0.19/0.50          | (v2_struct_0 @ X10))),
% 0.19/0.50      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.19/0.50  thf('25', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((v2_struct_0 @ sk_A)
% 0.19/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.50          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.19/0.50          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.19/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.50  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('28', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((v2_struct_0 @ sk_A)
% 0.19/0.50          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.19/0.50          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.19/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.19/0.50  thf('29', plain,
% 0.19/0.50      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.19/0.50         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.19/0.50         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['22', '28'])).
% 0.19/0.50  thf('30', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('31', plain,
% 0.19/0.50      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A)))
% 0.19/0.50         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.50      inference('demod', [status(thm)], ['29', '30'])).
% 0.19/0.50  thf('32', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('33', plain,
% 0.19/0.50      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.19/0.50         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.50      inference('clc', [status(thm)], ['31', '32'])).
% 0.19/0.50  thf(l1_zfmisc_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.19/0.50  thf('34', plain,
% 0.19/0.50      (![X0 : $i, X2 : $i]:
% 0.19/0.50         ((r1_tarski @ (k1_tarski @ X0) @ X2) | ~ (r2_hidden @ X0 @ X2))),
% 0.19/0.50      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.19/0.50  thf('35', plain,
% 0.19/0.50      (((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.19/0.50         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.50  thf('36', plain,
% 0.19/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.19/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.19/0.50  thf('37', plain,
% 0.19/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.19/0.50          | ~ (r1_tarski @ X12 @ (k1_tops_1 @ X13 @ X14))
% 0.19/0.50          | (m2_connsp_2 @ X14 @ X13 @ X12)
% 0.19/0.50          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.19/0.50          | ~ (l1_pre_topc @ X13)
% 0.19/0.50          | ~ (v2_pre_topc @ X13))),
% 0.19/0.50      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.19/0.50  thf('38', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.50          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.19/0.50          | ~ (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.50  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('41', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.50          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.19/0.50          | ~ (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.19/0.50  thf('42', plain,
% 0.19/0.50      ((((m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.19/0.50         | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.50         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.19/0.50         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['35', '41'])).
% 0.19/0.50  thf('43', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('44', plain,
% 0.19/0.50      ((((m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.19/0.50         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.19/0.50         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.50      inference('demod', [status(thm)], ['42', '43'])).
% 0.19/0.50  thf('45', plain,
% 0.19/0.50      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.50  thf('46', plain,
% 0.19/0.50      ((~ (m2_connsp_2 @ sk_C @ sk_A @ 
% 0.19/0.50           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.19/0.50         <= (~
% 0.19/0.50             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.19/0.50               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.19/0.50      inference('split', [status(esa)], ['20'])).
% 0.19/0.50  thf('47', plain,
% 0.19/0.50      (((~ (m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.19/0.50         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.19/0.50         <= (~
% 0.19/0.50             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.19/0.50               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['45', '46'])).
% 0.19/0.50  thf('48', plain,
% 0.19/0.50      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.19/0.50         <= (~
% 0.19/0.50             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.19/0.50               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.19/0.50             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['44', '47'])).
% 0.19/0.50  thf('49', plain,
% 0.19/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.19/0.50         <= (~
% 0.19/0.50             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.19/0.50               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.19/0.50             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['48'])).
% 0.19/0.50  thf(fc2_struct_0, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.50       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.19/0.50  thf('50', plain,
% 0.19/0.50      (![X4 : $i]:
% 0.19/0.50         (~ (v1_xboole_0 @ (u1_struct_0 @ X4))
% 0.19/0.50          | ~ (l1_struct_0 @ X4)
% 0.19/0.50          | (v2_struct_0 @ X4))),
% 0.19/0.50      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.19/0.50  thf('51', plain,
% 0.19/0.50      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.19/0.50         <= (~
% 0.19/0.50             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.19/0.50               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.19/0.50             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['49', '50'])).
% 0.19/0.50  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(dt_l1_pre_topc, axiom,
% 0.19/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.19/0.50  thf('53', plain, (![X3 : $i]: ((l1_struct_0 @ X3) | ~ (l1_pre_topc @ X3))),
% 0.19/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.19/0.50  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.50      inference('sup-', [status(thm)], ['52', '53'])).
% 0.19/0.50  thf('55', plain,
% 0.19/0.50      (((v2_struct_0 @ sk_A))
% 0.19/0.50         <= (~
% 0.19/0.50             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.19/0.50               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.19/0.50             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.50      inference('demod', [status(thm)], ['51', '54'])).
% 0.19/0.50  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('57', plain,
% 0.19/0.50      (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.19/0.50         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) | 
% 0.19/0.50       ~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.50      inference('sup-', [status(thm)], ['55', '56'])).
% 0.19/0.50  thf('58', plain,
% 0.19/0.50      (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.19/0.50         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) | 
% 0.19/0.50       ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.50      inference('split', [status(esa)], ['17'])).
% 0.19/0.50  thf('59', plain,
% 0.19/0.50      (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.19/0.50         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.19/0.50      inference('sat_resolution*', [status(thm)], ['21', '57', '58'])).
% 0.19/0.50  thf('60', plain,
% 0.19/0.50      (((m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.19/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('simpl_trail', [status(thm)], ['19', '59'])).
% 0.19/0.50  thf('61', plain,
% 0.19/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.19/0.50      inference('clc', [status(thm)], ['15', '60'])).
% 0.19/0.50  thf('62', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((r2_hidden @ X0 @ X1) | ~ (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.19/0.50  thf('63', plain,
% 0.19/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['61', '62'])).
% 0.19/0.50  thf('64', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('65', plain,
% 0.19/0.50      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.19/0.50          | ~ (r2_hidden @ X9 @ (k1_tops_1 @ X10 @ X11))
% 0.19/0.50          | (m1_connsp_2 @ X11 @ X10 @ X9)
% 0.19/0.50          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.19/0.50          | ~ (l1_pre_topc @ X10)
% 0.19/0.50          | ~ (v2_pre_topc @ X10)
% 0.19/0.50          | (v2_struct_0 @ X10))),
% 0.19/0.50      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.19/0.50  thf('66', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((v2_struct_0 @ sk_A)
% 0.19/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.50          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.19/0.50          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.19/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.19/0.50  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('69', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((v2_struct_0 @ sk_A)
% 0.19/0.50          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.19/0.50          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.19/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.19/0.50  thf('70', plain,
% 0.19/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | (m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.19/0.50        | (v2_struct_0 @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['63', '69'])).
% 0.19/0.50  thf('71', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('72', plain,
% 0.19/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.50        | (m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.19/0.50        | (v2_struct_0 @ sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['70', '71'])).
% 0.19/0.50  thf('73', plain,
% 0.19/0.50      ((~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 0.19/0.50         <= (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.19/0.50      inference('split', [status(esa)], ['20'])).
% 0.19/0.50  thf('74', plain, (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.19/0.50      inference('sat_resolution*', [status(thm)], ['21', '57'])).
% 0.19/0.50  thf('75', plain, (~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B)),
% 0.19/0.50      inference('simpl_trail', [status(thm)], ['73', '74'])).
% 0.19/0.50  thf('76', plain,
% 0.19/0.50      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.50      inference('clc', [status(thm)], ['72', '75'])).
% 0.19/0.50  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('78', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.19/0.50      inference('clc', [status(thm)], ['76', '77'])).
% 0.19/0.50  thf('79', plain,
% 0.19/0.50      (![X4 : $i]:
% 0.19/0.50         (~ (v1_xboole_0 @ (u1_struct_0 @ X4))
% 0.19/0.50          | ~ (l1_struct_0 @ X4)
% 0.19/0.50          | (v2_struct_0 @ X4))),
% 0.19/0.50      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.19/0.50  thf('80', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['78', '79'])).
% 0.19/0.50  thf('81', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.50      inference('sup-', [status(thm)], ['52', '53'])).
% 0.19/0.50  thf('82', plain, ((v2_struct_0 @ sk_A)),
% 0.19/0.50      inference('demod', [status(thm)], ['80', '81'])).
% 0.19/0.50  thf('83', plain, ($false), inference('demod', [status(thm)], ['0', '82'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
