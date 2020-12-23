%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FBcO0BGdWT

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:01 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 282 expanded)
%              Number of leaves         :   27 (  90 expanded)
%              Depth                    :   26
%              Number of atoms          :  926 (3994 expanded)
%              Number of equality atoms :    4 (   9 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m2_connsp_2_type,type,(
    m2_connsp_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

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

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m2_connsp_2 @ X18 @ X17 @ X16 )
      | ( r1_tarski @ X16 @ ( k1_tops_1 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
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
      | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( ( k6_domain_1 @ X11 @ X12 )
        = ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('17',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['17','19'])).

thf('21',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['18'])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_connsp_2 @ X15 @ X14 @ X13 )
      | ( r2_hidden @ X13 @ ( k1_tops_1 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
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
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('36',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('38',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( r1_tarski @ X16 @ ( k1_tops_1 @ X17 @ X18 ) )
      | ( m2_connsp_2 @ X18 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_connsp_2])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m2_connsp_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('47',plain,
    ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
   <= ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(split,[status(esa)],['21'])).

thf('48',plain,
    ( ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('51',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('52',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('54',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('55',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      & ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['18'])).

thf('60',plain,(
    m2_connsp_2 @ sk_C @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['22','58','59'])).

thf('61',plain,
    ( ( m2_connsp_2 @ sk_C @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['20','60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(clc,[status(thm)],['14','61'])).

thf('63',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('64',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r2_hidden @ X13 @ ( k1_tops_1 @ X14 @ X15 ) )
      | ( m1_connsp_2 @ X15 @ X14 @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B )
   <= ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['21'])).

thf('75',plain,(
    ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['22','58'])).

thf('76',plain,(
    ~ ( m1_connsp_2 @ sk_C @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['73','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('81',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['53','54'])).

thf('83',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    $false ),
    inference(demod,[status(thm)],['0','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FBcO0BGdWT
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:36:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.36/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.53  % Solved by: fo/fo7.sh
% 0.36/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.53  % done 96 iterations in 0.069s
% 0.36/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.53  % SZS output start Refutation
% 0.36/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.53  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.36/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.53  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.36/0.53  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.53  thf(m2_connsp_2_type, type, m2_connsp_2: $i > $i > $i > $o).
% 0.36/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.36/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.53  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.36/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.53  thf(t10_connsp_2, conjecture,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.53           ( ![C:$i]:
% 0.36/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.53               ( ( m2_connsp_2 @
% 0.36/0.53                   C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.36/0.53                 ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ))).
% 0.36/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.53    (~( ![A:$i]:
% 0.36/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.36/0.53            ( l1_pre_topc @ A ) ) =>
% 0.36/0.53          ( ![B:$i]:
% 0.36/0.53            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.53              ( ![C:$i]:
% 0.36/0.53                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.53                  ( ( m2_connsp_2 @
% 0.36/0.53                      C @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) <=>
% 0.36/0.53                    ( m1_connsp_2 @ C @ A @ B ) ) ) ) ) ) ) )),
% 0.36/0.53    inference('cnf.neg', [status(esa)], [t10_connsp_2])).
% 0.36/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('1', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(t2_subset, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( m1_subset_1 @ A @ B ) =>
% 0.36/0.53       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.36/0.53  thf('3', plain,
% 0.36/0.53      (![X4 : $i, X5 : $i]:
% 0.36/0.53         ((r2_hidden @ X4 @ X5)
% 0.36/0.53          | (v1_xboole_0 @ X5)
% 0.36/0.53          | ~ (m1_subset_1 @ X4 @ X5))),
% 0.36/0.53      inference('cnf', [status(esa)], [t2_subset])).
% 0.36/0.53  thf('4', plain,
% 0.36/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.53        | (r2_hidden @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.53  thf(l1_zfmisc_1, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.36/0.53  thf('5', plain,
% 0.36/0.53      (![X1 : $i, X3 : $i]:
% 0.36/0.53         ((r1_tarski @ (k1_tarski @ X1) @ X3) | ~ (r2_hidden @ X1 @ X3))),
% 0.36/0.53      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.36/0.53  thf('6', plain,
% 0.36/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.53        | (r1_tarski @ (k1_tarski @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.53  thf(t3_subset, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.53  thf('7', plain,
% 0.36/0.53      (![X6 : $i, X8 : $i]:
% 0.36/0.53         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.36/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.53  thf('8', plain,
% 0.36/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.53        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.36/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.53  thf(d2_connsp_2, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.53           ( ![C:$i]:
% 0.36/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.53               ( ( m2_connsp_2 @ C @ A @ B ) <=>
% 0.36/0.53                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.36/0.53  thf('9', plain,
% 0.36/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.36/0.53          | ~ (m2_connsp_2 @ X18 @ X17 @ X16)
% 0.36/0.53          | (r1_tarski @ X16 @ (k1_tops_1 @ X17 @ X18))
% 0.36/0.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.36/0.53          | ~ (l1_pre_topc @ X17)
% 0.36/0.53          | ~ (v2_pre_topc @ X17))),
% 0.36/0.53      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.36/0.53  thf('10', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.53          | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.36/0.53          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.53  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('13', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.53          | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0))
% 0.36/0.53          | ~ (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.36/0.53      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.36/0.53  thf('14', plain,
% 0.36/0.53      ((~ (m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.36/0.53        | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C))
% 0.36/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['1', '13'])).
% 0.36/0.53  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(redefinition_k6_domain_1, axiom,
% 0.36/0.53    (![A:$i,B:$i]:
% 0.36/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.36/0.53       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.36/0.53  thf('16', plain,
% 0.36/0.53      (![X11 : $i, X12 : $i]:
% 0.36/0.53         ((v1_xboole_0 @ X11)
% 0.36/0.53          | ~ (m1_subset_1 @ X12 @ X11)
% 0.36/0.53          | ((k6_domain_1 @ X11 @ X12) = (k1_tarski @ X12)))),
% 0.36/0.53      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.36/0.53  thf('17', plain,
% 0.36/0.53      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.36/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.53  thf('18', plain,
% 0.36/0.53      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.36/0.53        | (m2_connsp_2 @ sk_C @ sk_A @ 
% 0.36/0.53           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('19', plain,
% 0.36/0.53      (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.36/0.53         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.36/0.53         <= (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.36/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.36/0.53      inference('split', [status(esa)], ['18'])).
% 0.36/0.53  thf('20', plain,
% 0.36/0.53      ((((m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.36/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.36/0.53         <= (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.36/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.36/0.53      inference('sup+', [status(thm)], ['17', '19'])).
% 0.36/0.53  thf('21', plain,
% 0.36/0.53      ((~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.36/0.53        | ~ (m2_connsp_2 @ sk_C @ sk_A @ 
% 0.36/0.53             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('22', plain,
% 0.36/0.53      (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)) | 
% 0.36/0.53       ~
% 0.36/0.53       ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.36/0.53         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.36/0.53      inference('split', [status(esa)], ['21'])).
% 0.36/0.53  thf('23', plain,
% 0.36/0.53      (((m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 0.36/0.53         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.36/0.53      inference('split', [status(esa)], ['18'])).
% 0.36/0.53  thf('24', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(d1_connsp_2, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.53       ( ![B:$i]:
% 0.36/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.36/0.53           ( ![C:$i]:
% 0.36/0.53             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.53               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.36/0.53                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.36/0.53  thf('25', plain,
% 0.36/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.36/0.53          | ~ (m1_connsp_2 @ X15 @ X14 @ X13)
% 0.36/0.53          | (r2_hidden @ X13 @ (k1_tops_1 @ X14 @ X15))
% 0.36/0.53          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.36/0.53          | ~ (l1_pre_topc @ X14)
% 0.36/0.53          | ~ (v2_pre_topc @ X14)
% 0.36/0.53          | (v2_struct_0 @ X14))),
% 0.36/0.53      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.36/0.53  thf('26', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         ((v2_struct_0 @ sk_A)
% 0.36/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.53          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.36/0.53          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.36/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.53  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('29', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         ((v2_struct_0 @ sk_A)
% 0.36/0.53          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.36/0.53          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.36/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.36/0.53  thf('30', plain,
% 0.36/0.53      (((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.36/0.53         | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.36/0.53         | (v2_struct_0 @ sk_A))) <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['23', '29'])).
% 0.36/0.53  thf('31', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('32', plain,
% 0.36/0.53      ((((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A)))
% 0.36/0.53         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.36/0.53      inference('demod', [status(thm)], ['30', '31'])).
% 0.36/0.53  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('34', plain,
% 0.36/0.53      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.36/0.53         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.36/0.53      inference('clc', [status(thm)], ['32', '33'])).
% 0.36/0.53  thf('35', plain,
% 0.36/0.53      (![X1 : $i, X3 : $i]:
% 0.36/0.53         ((r1_tarski @ (k1_tarski @ X1) @ X3) | ~ (r2_hidden @ X1 @ X3))),
% 0.36/0.53      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.36/0.53  thf('36', plain,
% 0.36/0.53      (((r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.36/0.53         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['34', '35'])).
% 0.36/0.53  thf('37', plain,
% 0.36/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.53        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.36/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.36/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.36/0.53  thf('38', plain,
% 0.36/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.36/0.53          | ~ (r1_tarski @ X16 @ (k1_tops_1 @ X17 @ X18))
% 0.36/0.53          | (m2_connsp_2 @ X18 @ X17 @ X16)
% 0.36/0.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.36/0.53          | ~ (l1_pre_topc @ X17)
% 0.36/0.53          | ~ (v2_pre_topc @ X17))),
% 0.36/0.53      inference('cnf', [status(esa)], [d2_connsp_2])).
% 0.36/0.53  thf('39', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.53          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.36/0.53          | ~ (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.36/0.53  thf('40', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('42', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.53          | (m2_connsp_2 @ X0 @ sk_A @ (k1_tarski @ sk_B))
% 0.36/0.53          | ~ (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ X0)))),
% 0.36/0.53      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.36/0.53  thf('43', plain,
% 0.36/0.53      ((((m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.36/0.53         | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.36/0.53         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['36', '42'])).
% 0.36/0.53  thf('44', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('45', plain,
% 0.36/0.53      ((((m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.36/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.36/0.53         <= (((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.36/0.53      inference('demod', [status(thm)], ['43', '44'])).
% 0.36/0.53  thf('46', plain,
% 0.36/0.53      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.36/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.53  thf('47', plain,
% 0.36/0.53      ((~ (m2_connsp_2 @ sk_C @ sk_A @ 
% 0.36/0.53           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.36/0.53         <= (~
% 0.36/0.53             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.36/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.36/0.53      inference('split', [status(esa)], ['21'])).
% 0.36/0.53  thf('48', plain,
% 0.36/0.53      (((~ (m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.36/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.36/0.53         <= (~
% 0.36/0.53             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.36/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.36/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.36/0.53  thf('49', plain,
% 0.36/0.53      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.36/0.53         <= (~
% 0.36/0.53             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.36/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.36/0.53             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['45', '48'])).
% 0.36/0.53  thf('50', plain,
% 0.36/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.36/0.53         <= (~
% 0.36/0.53             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.36/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.36/0.53             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.36/0.53      inference('simplify', [status(thm)], ['49'])).
% 0.36/0.53  thf(fc2_struct_0, axiom,
% 0.36/0.53    (![A:$i]:
% 0.36/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.36/0.53       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.53  thf('51', plain,
% 0.36/0.53      (![X10 : $i]:
% 0.36/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X10))
% 0.36/0.53          | ~ (l1_struct_0 @ X10)
% 0.36/0.53          | (v2_struct_0 @ X10))),
% 0.36/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.36/0.53  thf('52', plain,
% 0.36/0.53      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.36/0.53         <= (~
% 0.36/0.53             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.36/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.36/0.53             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.53  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf(dt_l1_pre_topc, axiom,
% 0.36/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.36/0.53  thf('54', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.36/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.36/0.53  thf('55', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.53      inference('sup-', [status(thm)], ['53', '54'])).
% 0.36/0.53  thf('56', plain,
% 0.36/0.53      (((v2_struct_0 @ sk_A))
% 0.36/0.53         <= (~
% 0.36/0.53             ((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.36/0.53               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) & 
% 0.36/0.53             ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.36/0.53      inference('demod', [status(thm)], ['52', '55'])).
% 0.36/0.53  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('58', plain,
% 0.36/0.53      (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.36/0.53         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) | 
% 0.36/0.53       ~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.36/0.53      inference('sup-', [status(thm)], ['56', '57'])).
% 0.36/0.53  thf('59', plain,
% 0.36/0.53      (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.36/0.53         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))) | 
% 0.36/0.53       ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.36/0.53      inference('split', [status(esa)], ['18'])).
% 0.36/0.53  thf('60', plain,
% 0.36/0.53      (((m2_connsp_2 @ sk_C @ sk_A @ 
% 0.36/0.53         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.36/0.53      inference('sat_resolution*', [status(thm)], ['22', '58', '59'])).
% 0.36/0.53  thf('61', plain,
% 0.36/0.53      (((m2_connsp_2 @ sk_C @ sk_A @ (k1_tarski @ sk_B))
% 0.36/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('simpl_trail', [status(thm)], ['20', '60'])).
% 0.36/0.53  thf('62', plain,
% 0.36/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.53        | (r1_tarski @ (k1_tarski @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.36/0.53      inference('clc', [status(thm)], ['14', '61'])).
% 0.36/0.53  thf('63', plain,
% 0.36/0.53      (![X1 : $i, X2 : $i]:
% 0.36/0.53         ((r2_hidden @ X1 @ X2) | ~ (r1_tarski @ (k1_tarski @ X1) @ X2))),
% 0.36/0.53      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.36/0.53  thf('64', plain,
% 0.36/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.53        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['62', '63'])).
% 0.36/0.53  thf('65', plain,
% 0.36/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('66', plain,
% 0.36/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.53         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.36/0.53          | ~ (r2_hidden @ X13 @ (k1_tops_1 @ X14 @ X15))
% 0.36/0.53          | (m1_connsp_2 @ X15 @ X14 @ X13)
% 0.36/0.53          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.36/0.53          | ~ (l1_pre_topc @ X14)
% 0.36/0.53          | ~ (v2_pre_topc @ X14)
% 0.36/0.53          | (v2_struct_0 @ X14))),
% 0.36/0.53      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.36/0.53  thf('67', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         ((v2_struct_0 @ sk_A)
% 0.36/0.53          | ~ (v2_pre_topc @ sk_A)
% 0.36/0.53          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.53          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.36/0.53          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.36/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('sup-', [status(thm)], ['65', '66'])).
% 0.36/0.53  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('70', plain,
% 0.36/0.53      (![X0 : $i]:
% 0.36/0.53         ((v2_struct_0 @ sk_A)
% 0.36/0.53          | (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.36/0.53          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.36/0.53          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.36/0.53  thf('71', plain,
% 0.36/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.53        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.36/0.53        | (m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.36/0.53        | (v2_struct_0 @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['64', '70'])).
% 0.36/0.53  thf('72', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('73', plain,
% 0.36/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.36/0.53        | (m1_connsp_2 @ sk_C @ sk_A @ sk_B)
% 0.36/0.53        | (v2_struct_0 @ sk_A))),
% 0.36/0.53      inference('demod', [status(thm)], ['71', '72'])).
% 0.36/0.53  thf('74', plain,
% 0.36/0.53      ((~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B))
% 0.36/0.53         <= (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)))),
% 0.36/0.53      inference('split', [status(esa)], ['21'])).
% 0.36/0.53  thf('75', plain, (~ ((m1_connsp_2 @ sk_C @ sk_A @ sk_B))),
% 0.36/0.53      inference('sat_resolution*', [status(thm)], ['22', '58'])).
% 0.36/0.53  thf('76', plain, (~ (m1_connsp_2 @ sk_C @ sk_A @ sk_B)),
% 0.36/0.53      inference('simpl_trail', [status(thm)], ['74', '75'])).
% 0.36/0.53  thf('77', plain,
% 0.36/0.53      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.53      inference('clc', [status(thm)], ['73', '76'])).
% 0.36/0.53  thf('78', plain, (~ (v2_struct_0 @ sk_A)),
% 0.36/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.53  thf('79', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.36/0.53      inference('clc', [status(thm)], ['77', '78'])).
% 0.36/0.53  thf('80', plain,
% 0.36/0.53      (![X10 : $i]:
% 0.36/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X10))
% 0.36/0.53          | ~ (l1_struct_0 @ X10)
% 0.36/0.53          | (v2_struct_0 @ X10))),
% 0.36/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.36/0.53  thf('81', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.53      inference('sup-', [status(thm)], ['79', '80'])).
% 0.36/0.53  thf('82', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.53      inference('sup-', [status(thm)], ['53', '54'])).
% 0.36/0.53  thf('83', plain, ((v2_struct_0 @ sk_A)),
% 0.36/0.53      inference('demod', [status(thm)], ['81', '82'])).
% 0.36/0.53  thf('84', plain, ($false), inference('demod', [status(thm)], ['0', '83'])).
% 0.36/0.53  
% 0.36/0.53  % SZS output end Refutation
% 0.36/0.53  
% 0.36/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
