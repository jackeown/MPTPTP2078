%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dwj3wlvivh

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:34 EST 2020

% Result     : Theorem 2.03s
% Output     : Refutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 654 expanded)
%              Number of leaves         :   27 ( 194 expanded)
%              Depth                    :   16
%              Number of atoms          :  871 (9168 expanded)
%              Number of equality atoms :   27 ( 498 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t12_compts_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( B = k1_xboole_0 )
             => ( ( v2_compts_1 @ B @ A )
              <=> ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) )
            & ( ( v2_pre_topc @ A )
             => ( ( B = k1_xboole_0 )
                | ( ( v2_compts_1 @ B @ A )
                <=> ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( ( B = k1_xboole_0 )
               => ( ( v2_compts_1 @ B @ A )
                <=> ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) )
              & ( ( v2_pre_topc @ A )
               => ( ( B = k1_xboole_0 )
                  | ( ( v2_compts_1 @ B @ A )
                  <=> ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_compts_1])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X13 @ X12 ) )
        = X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
    | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X7 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('9',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['9','10'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( l1_pre_topc @ X10 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('16',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('17',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['6','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t11_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ C @ ( k2_struct_0 @ B ) )
               => ( ( v2_compts_1 @ C @ A )
                <=> ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( ( D = C )
                       => ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ ( k2_struct_0 @ X18 ) )
      | ~ ( v2_compts_1 @ ( sk_D @ X20 @ X18 ) @ X18 )
      | ( v2_compts_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_compts_1 @ sk_B @ sk_A )
      | ~ ( v2_compts_1 @ ( sk_D @ sk_B @ X0 ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ sk_B @ sk_A )
      | ~ ( v2_compts_1 @ ( sk_D @ sk_B @ X0 ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_compts_1 @ ( sk_D @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['9','10'])).

thf('28',plain,
    ( ~ ( v2_compts_1 @ ( sk_D @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['24','26','27'])).

thf('29',plain,
    ( ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( v2_compts_1 @ sk_B @ sk_A )
   <= ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['29'])).

thf('32',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['3','4'])).

thf('33',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
    | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
   <= ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ ( k2_struct_0 @ X18 ) )
      | ~ ( v2_compts_1 @ X20 @ X19 )
      | ( X21 != X20 )
      | ( v2_compts_1 @ X21 @ X18 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('37',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v2_compts_1 @ X20 @ X18 )
      | ~ ( v2_compts_1 @ X20 @ X19 )
      | ~ ( r1_tarski @ X20 @ ( k2_struct_0 @ X18 ) )
      | ~ ( m1_pre_topc @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ X0 ) )
      | ~ ( v2_compts_1 @ sk_B @ sk_A )
      | ( v2_compts_1 @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ X0 ) )
      | ~ ( v2_compts_1 @ sk_B @ sk_A )
      | ( v2_compts_1 @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ( v2_compts_1 @ sk_B @ X0 )
        | ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_A ) )
   <= ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
      | ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
      | ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
   <= ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','41'])).

thf('43',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['9','10'])).

thf('47',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['6','17'])).

thf('48',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('49',plain,
    ( ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['42','45','46','47','48'])).

thf('50',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['6','17'])).

thf(t10_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_compts_1 @ A )
      <=> ( v2_compts_1 @ ( k2_struct_0 @ A ) @ A ) ) ) )).

thf('51',plain,(
    ! [X17: $i] :
      ( ~ ( v2_compts_1 @ ( k2_struct_0 @ X17 ) @ X17 )
      | ( v1_compts_1 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t10_compts_1])).

thf('52',plain,
    ( ~ ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('54',plain,
    ( ~ ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,
    ( ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['29'])).

thf('57',plain,
    ( ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['31','57'])).

thf('59',plain,(
    ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['30','58'])).

thf('60',plain,(
    ~ ( v2_compts_1 @ ( sk_D @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['28','59'])).

thf('61',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['6','17'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ ( k2_struct_0 @ X18 ) )
      | ( ( sk_D @ X20 @ X18 )
        = X20 )
      | ( v2_compts_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t11_compts_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( v2_compts_1 @ sk_B @ sk_A )
      | ( ( sk_D @ sk_B @ X0 )
        = sk_B )
      | ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_compts_1 @ sk_B @ sk_A )
      | ( ( sk_D @ sk_B @ X0 )
        = sk_B )
      | ~ ( r1_tarski @ sk_B @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( ( sk_D @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
    | ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('69',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['9','10'])).

thf('70',plain,
    ( ( ( sk_D @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
    | ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['30','58'])).

thf('72',plain,
    ( ( sk_D @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['33'])).

thf('74',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['6','17'])).

thf('75',plain,(
    ! [X17: $i] :
      ( ~ ( v1_compts_1 @ X17 )
      | ( v2_compts_1 @ ( k2_struct_0 @ X17 ) @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t10_compts_1])).

thf('76',plain,
    ( ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('78',plain,
    ( ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,
    ( ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['33'])).

thf('81',plain,(
    v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['31','57','80'])).

thf('82',plain,(
    v2_compts_1 @ sk_B @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['79','81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['60','72','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dwj3wlvivh
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:19:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 2.03/2.23  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.03/2.23  % Solved by: fo/fo7.sh
% 2.03/2.23  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.03/2.23  % done 1807 iterations in 1.730s
% 2.03/2.23  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.03/2.23  % SZS output start Refutation
% 2.03/2.23  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.03/2.23  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 2.03/2.23  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 2.03/2.23  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.03/2.23  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 2.03/2.23  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 2.03/2.23  thf(sk_A_type, type, sk_A: $i).
% 2.03/2.23  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.03/2.23  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 2.03/2.23  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.03/2.23  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.03/2.23  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 2.03/2.23  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.03/2.23  thf(sk_B_type, type, sk_B: $i).
% 2.03/2.23  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 2.03/2.23  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.03/2.23  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.03/2.23  thf(d3_struct_0, axiom,
% 2.03/2.23    (![A:$i]:
% 2.03/2.23     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 2.03/2.23  thf('0', plain,
% 2.03/2.23      (![X6 : $i]:
% 2.03/2.23         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 2.03/2.23      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.03/2.23  thf(t12_compts_1, conjecture,
% 2.03/2.23    (![A:$i]:
% 2.03/2.23     ( ( l1_pre_topc @ A ) =>
% 2.03/2.23       ( ![B:$i]:
% 2.03/2.23         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.03/2.23           ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.03/2.23               ( ( v2_compts_1 @ B @ A ) <=>
% 2.03/2.23                 ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) & 
% 2.03/2.23             ( ( v2_pre_topc @ A ) =>
% 2.03/2.23               ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.03/2.23                 ( ( v2_compts_1 @ B @ A ) <=>
% 2.03/2.23                   ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) ) ) ))).
% 2.03/2.23  thf(zf_stmt_0, negated_conjecture,
% 2.03/2.23    (~( ![A:$i]:
% 2.03/2.23        ( ( l1_pre_topc @ A ) =>
% 2.03/2.23          ( ![B:$i]:
% 2.03/2.23            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.03/2.23              ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.03/2.23                  ( ( v2_compts_1 @ B @ A ) <=>
% 2.03/2.23                    ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) & 
% 2.03/2.23                ( ( v2_pre_topc @ A ) =>
% 2.03/2.23                  ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.03/2.23                    ( ( v2_compts_1 @ B @ A ) <=>
% 2.03/2.23                      ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) ) ) ) )),
% 2.03/2.23    inference('cnf.neg', [status(esa)], [t12_compts_1])).
% 2.03/2.23  thf('1', plain,
% 2.03/2.23      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.03/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.23  thf(t29_pre_topc, axiom,
% 2.03/2.23    (![A:$i]:
% 2.03/2.23     ( ( l1_pre_topc @ A ) =>
% 2.03/2.23       ( ![B:$i]:
% 2.03/2.23         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.03/2.23           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 2.03/2.23  thf('2', plain,
% 2.03/2.23      (![X12 : $i, X13 : $i]:
% 2.03/2.23         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 2.03/2.23          | ((u1_struct_0 @ (k1_pre_topc @ X13 @ X12)) = (X12))
% 2.03/2.23          | ~ (l1_pre_topc @ X13))),
% 2.03/2.23      inference('cnf', [status(esa)], [t29_pre_topc])).
% 2.03/2.23  thf('3', plain,
% 2.03/2.23      ((~ (l1_pre_topc @ sk_A)
% 2.03/2.23        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B)))),
% 2.03/2.23      inference('sup-', [status(thm)], ['1', '2'])).
% 2.03/2.23  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 2.03/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.23  thf('5', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 2.03/2.23      inference('demod', [status(thm)], ['3', '4'])).
% 2.03/2.23  thf('6', plain,
% 2.03/2.23      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 2.03/2.23        | ~ (l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 2.03/2.23      inference('sup+', [status(thm)], ['0', '5'])).
% 2.03/2.23  thf('7', plain,
% 2.03/2.23      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.03/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.23  thf(dt_k1_pre_topc, axiom,
% 2.03/2.23    (![A:$i,B:$i]:
% 2.03/2.23     ( ( ( l1_pre_topc @ A ) & 
% 2.03/2.23         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.03/2.23       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 2.03/2.23         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 2.03/2.23  thf('8', plain,
% 2.03/2.23      (![X7 : $i, X8 : $i]:
% 2.03/2.23         (~ (l1_pre_topc @ X7)
% 2.03/2.23          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 2.03/2.23          | (m1_pre_topc @ (k1_pre_topc @ X7 @ X8) @ X7))),
% 2.03/2.23      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 2.03/2.23  thf('9', plain,
% 2.03/2.23      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 2.03/2.23        | ~ (l1_pre_topc @ sk_A))),
% 2.03/2.23      inference('sup-', [status(thm)], ['7', '8'])).
% 2.03/2.23  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 2.03/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.23  thf('11', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 2.03/2.23      inference('demod', [status(thm)], ['9', '10'])).
% 2.03/2.23  thf(dt_m1_pre_topc, axiom,
% 2.03/2.23    (![A:$i]:
% 2.03/2.23     ( ( l1_pre_topc @ A ) =>
% 2.03/2.23       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 2.03/2.23  thf('12', plain,
% 2.03/2.23      (![X10 : $i, X11 : $i]:
% 2.03/2.23         (~ (m1_pre_topc @ X10 @ X11)
% 2.03/2.23          | (l1_pre_topc @ X10)
% 2.03/2.23          | ~ (l1_pre_topc @ X11))),
% 2.03/2.23      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 2.03/2.23  thf('13', plain,
% 2.03/2.23      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))),
% 2.03/2.23      inference('sup-', [status(thm)], ['11', '12'])).
% 2.03/2.23  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 2.03/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.23  thf('15', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 2.03/2.23      inference('demod', [status(thm)], ['13', '14'])).
% 2.03/2.23  thf(dt_l1_pre_topc, axiom,
% 2.03/2.23    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 2.03/2.23  thf('16', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 2.03/2.23      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 2.03/2.23  thf('17', plain, ((l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))),
% 2.03/2.23      inference('sup-', [status(thm)], ['15', '16'])).
% 2.03/2.23  thf('18', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 2.03/2.23      inference('demod', [status(thm)], ['6', '17'])).
% 2.03/2.23  thf('19', plain,
% 2.03/2.23      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.03/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.23  thf(t11_compts_1, axiom,
% 2.03/2.23    (![A:$i]:
% 2.03/2.23     ( ( l1_pre_topc @ A ) =>
% 2.03/2.23       ( ![B:$i]:
% 2.03/2.23         ( ( m1_pre_topc @ B @ A ) =>
% 2.03/2.23           ( ![C:$i]:
% 2.03/2.23             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.03/2.23               ( ( r1_tarski @ C @ ( k2_struct_0 @ B ) ) =>
% 2.03/2.23                 ( ( v2_compts_1 @ C @ A ) <=>
% 2.03/2.23                   ( ![D:$i]:
% 2.03/2.23                     ( ( m1_subset_1 @
% 2.03/2.23                         D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 2.03/2.23                       ( ( ( D ) = ( C ) ) => ( v2_compts_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 2.03/2.23  thf('20', plain,
% 2.03/2.23      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.03/2.23         (~ (m1_pre_topc @ X18 @ X19)
% 2.03/2.23          | ~ (r1_tarski @ X20 @ (k2_struct_0 @ X18))
% 2.03/2.23          | ~ (v2_compts_1 @ (sk_D @ X20 @ X18) @ X18)
% 2.03/2.23          | (v2_compts_1 @ X20 @ X19)
% 2.03/2.23          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 2.03/2.23          | ~ (l1_pre_topc @ X19))),
% 2.03/2.23      inference('cnf', [status(esa)], [t11_compts_1])).
% 2.03/2.23  thf('21', plain,
% 2.03/2.23      (![X0 : $i]:
% 2.03/2.23         (~ (l1_pre_topc @ sk_A)
% 2.03/2.23          | (v2_compts_1 @ sk_B @ sk_A)
% 2.03/2.23          | ~ (v2_compts_1 @ (sk_D @ sk_B @ X0) @ X0)
% 2.03/2.23          | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 2.03/2.23          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 2.03/2.23      inference('sup-', [status(thm)], ['19', '20'])).
% 2.03/2.23  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 2.03/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.23  thf('23', plain,
% 2.03/2.23      (![X0 : $i]:
% 2.03/2.23         ((v2_compts_1 @ sk_B @ sk_A)
% 2.03/2.23          | ~ (v2_compts_1 @ (sk_D @ sk_B @ X0) @ X0)
% 2.03/2.23          | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 2.03/2.23          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 2.03/2.23      inference('demod', [status(thm)], ['21', '22'])).
% 2.03/2.23  thf('24', plain,
% 2.03/2.23      ((~ (r1_tarski @ sk_B @ sk_B)
% 2.03/2.23        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 2.03/2.23        | ~ (v2_compts_1 @ (sk_D @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 2.03/2.23             (k1_pre_topc @ sk_A @ sk_B))
% 2.03/2.23        | (v2_compts_1 @ sk_B @ sk_A))),
% 2.03/2.23      inference('sup-', [status(thm)], ['18', '23'])).
% 2.03/2.23  thf(d10_xboole_0, axiom,
% 2.03/2.23    (![A:$i,B:$i]:
% 2.03/2.23     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.03/2.23  thf('25', plain,
% 2.03/2.23      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.03/2.23      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.03/2.23  thf('26', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.03/2.23      inference('simplify', [status(thm)], ['25'])).
% 2.03/2.23  thf('27', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 2.03/2.23      inference('demod', [status(thm)], ['9', '10'])).
% 2.03/2.23  thf('28', plain,
% 2.03/2.23      ((~ (v2_compts_1 @ (sk_D @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 2.03/2.23           (k1_pre_topc @ sk_A @ sk_B))
% 2.03/2.23        | (v2_compts_1 @ sk_B @ sk_A))),
% 2.03/2.23      inference('demod', [status(thm)], ['24', '26', '27'])).
% 2.03/2.23  thf('29', plain,
% 2.03/2.23      ((~ (v2_compts_1 @ sk_B @ sk_A)
% 2.03/2.23        | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 2.03/2.23        | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 2.03/2.23        | ~ (v2_compts_1 @ sk_B @ sk_A))),
% 2.03/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.23  thf('30', plain,
% 2.03/2.23      ((~ (v2_compts_1 @ sk_B @ sk_A)) <= (~ ((v2_compts_1 @ sk_B @ sk_A)))),
% 2.03/2.23      inference('split', [status(esa)], ['29'])).
% 2.03/2.23  thf('31', plain,
% 2.03/2.23      (~ ((v2_compts_1 @ sk_B @ sk_A)) | 
% 2.03/2.23       ~ ((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 2.03/2.23      inference('split', [status(esa)], ['29'])).
% 2.03/2.23  thf('32', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 2.03/2.23      inference('demod', [status(thm)], ['3', '4'])).
% 2.03/2.23  thf('33', plain,
% 2.03/2.23      (((v2_compts_1 @ sk_B @ sk_A)
% 2.03/2.23        | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 2.03/2.23        | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 2.03/2.23        | (v2_compts_1 @ sk_B @ sk_A))),
% 2.03/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.23  thf('34', plain,
% 2.03/2.23      (((v2_compts_1 @ sk_B @ sk_A)) <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 2.03/2.23      inference('split', [status(esa)], ['33'])).
% 2.03/2.23  thf('35', plain,
% 2.03/2.23      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.03/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.23  thf('36', plain,
% 2.03/2.23      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 2.03/2.23         (~ (m1_pre_topc @ X18 @ X19)
% 2.03/2.23          | ~ (r1_tarski @ X20 @ (k2_struct_0 @ X18))
% 2.03/2.23          | ~ (v2_compts_1 @ X20 @ X19)
% 2.03/2.23          | ((X21) != (X20))
% 2.03/2.23          | (v2_compts_1 @ X21 @ X18)
% 2.03/2.23          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 2.03/2.23          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 2.03/2.23          | ~ (l1_pre_topc @ X19))),
% 2.03/2.23      inference('cnf', [status(esa)], [t11_compts_1])).
% 2.03/2.23  thf('37', plain,
% 2.03/2.23      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.03/2.23         (~ (l1_pre_topc @ X19)
% 2.03/2.23          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 2.03/2.23          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 2.03/2.23          | (v2_compts_1 @ X20 @ X18)
% 2.03/2.23          | ~ (v2_compts_1 @ X20 @ X19)
% 2.03/2.23          | ~ (r1_tarski @ X20 @ (k2_struct_0 @ X18))
% 2.03/2.23          | ~ (m1_pre_topc @ X18 @ X19))),
% 2.03/2.23      inference('simplify', [status(thm)], ['36'])).
% 2.03/2.23  thf('38', plain,
% 2.03/2.23      (![X0 : $i]:
% 2.03/2.23         (~ (m1_pre_topc @ X0 @ sk_A)
% 2.03/2.23          | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 2.03/2.23          | ~ (v2_compts_1 @ sk_B @ sk_A)
% 2.03/2.23          | (v2_compts_1 @ sk_B @ X0)
% 2.03/2.23          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 2.03/2.23          | ~ (l1_pre_topc @ sk_A))),
% 2.03/2.23      inference('sup-', [status(thm)], ['35', '37'])).
% 2.03/2.23  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 2.03/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.23  thf('40', plain,
% 2.03/2.23      (![X0 : $i]:
% 2.03/2.23         (~ (m1_pre_topc @ X0 @ sk_A)
% 2.03/2.23          | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 2.03/2.23          | ~ (v2_compts_1 @ sk_B @ sk_A)
% 2.03/2.23          | (v2_compts_1 @ sk_B @ X0)
% 2.03/2.23          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 2.03/2.23      inference('demod', [status(thm)], ['38', '39'])).
% 2.03/2.23  thf('41', plain,
% 2.03/2.23      ((![X0 : $i]:
% 2.03/2.23          (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 2.03/2.23           | (v2_compts_1 @ sk_B @ X0)
% 2.03/2.23           | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 2.03/2.23           | ~ (m1_pre_topc @ X0 @ sk_A)))
% 2.03/2.23         <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 2.03/2.23      inference('sup-', [status(thm)], ['34', '40'])).
% 2.03/2.23  thf('42', plain,
% 2.03/2.23      (((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_B))
% 2.03/2.23         | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 2.03/2.23         | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))
% 2.03/2.23         | (v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))))
% 2.03/2.23         <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 2.03/2.23      inference('sup-', [status(thm)], ['32', '41'])).
% 2.03/2.23  thf('43', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.03/2.23      inference('simplify', [status(thm)], ['25'])).
% 2.03/2.23  thf(t3_subset, axiom,
% 2.03/2.23    (![A:$i,B:$i]:
% 2.03/2.23     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.03/2.23  thf('44', plain,
% 2.03/2.23      (![X3 : $i, X5 : $i]:
% 2.03/2.23         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 2.03/2.23      inference('cnf', [status(esa)], [t3_subset])).
% 2.03/2.23  thf('45', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.03/2.23      inference('sup-', [status(thm)], ['43', '44'])).
% 2.03/2.23  thf('46', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 2.03/2.23      inference('demod', [status(thm)], ['9', '10'])).
% 2.03/2.23  thf('47', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 2.03/2.23      inference('demod', [status(thm)], ['6', '17'])).
% 2.03/2.23  thf('48', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.03/2.23      inference('simplify', [status(thm)], ['25'])).
% 2.03/2.23  thf('49', plain,
% 2.03/2.23      (((v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)))
% 2.03/2.23         <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 2.03/2.23      inference('demod', [status(thm)], ['42', '45', '46', '47', '48'])).
% 2.03/2.23  thf('50', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 2.03/2.23      inference('demod', [status(thm)], ['6', '17'])).
% 2.03/2.23  thf(t10_compts_1, axiom,
% 2.03/2.23    (![A:$i]:
% 2.03/2.23     ( ( l1_pre_topc @ A ) =>
% 2.03/2.23       ( ( v1_compts_1 @ A ) <=> ( v2_compts_1 @ ( k2_struct_0 @ A ) @ A ) ) ))).
% 2.03/2.23  thf('51', plain,
% 2.03/2.23      (![X17 : $i]:
% 2.03/2.23         (~ (v2_compts_1 @ (k2_struct_0 @ X17) @ X17)
% 2.03/2.23          | (v1_compts_1 @ X17)
% 2.03/2.23          | ~ (l1_pre_topc @ X17))),
% 2.03/2.23      inference('cnf', [status(esa)], [t10_compts_1])).
% 2.03/2.23  thf('52', plain,
% 2.03/2.23      ((~ (v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))
% 2.03/2.23        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 2.03/2.23        | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 2.03/2.23      inference('sup-', [status(thm)], ['50', '51'])).
% 2.03/2.23  thf('53', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 2.03/2.23      inference('demod', [status(thm)], ['13', '14'])).
% 2.03/2.23  thf('54', plain,
% 2.03/2.23      ((~ (v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))
% 2.03/2.23        | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 2.03/2.23      inference('demod', [status(thm)], ['52', '53'])).
% 2.03/2.23  thf('55', plain,
% 2.03/2.23      (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))
% 2.03/2.23         <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 2.03/2.23      inference('sup-', [status(thm)], ['49', '54'])).
% 2.03/2.23  thf('56', plain,
% 2.03/2.23      ((~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))
% 2.03/2.23         <= (~ ((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))),
% 2.03/2.23      inference('split', [status(esa)], ['29'])).
% 2.03/2.23  thf('57', plain,
% 2.03/2.23      (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))) | 
% 2.03/2.23       ~ ((v2_compts_1 @ sk_B @ sk_A))),
% 2.03/2.23      inference('sup-', [status(thm)], ['55', '56'])).
% 2.03/2.23  thf('58', plain, (~ ((v2_compts_1 @ sk_B @ sk_A))),
% 2.03/2.23      inference('sat_resolution*', [status(thm)], ['31', '57'])).
% 2.03/2.23  thf('59', plain, (~ (v2_compts_1 @ sk_B @ sk_A)),
% 2.03/2.23      inference('simpl_trail', [status(thm)], ['30', '58'])).
% 2.03/2.23  thf('60', plain,
% 2.03/2.23      (~ (v2_compts_1 @ (sk_D @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 2.03/2.23          (k1_pre_topc @ sk_A @ sk_B))),
% 2.03/2.23      inference('clc', [status(thm)], ['28', '59'])).
% 2.03/2.23  thf('61', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 2.03/2.23      inference('demod', [status(thm)], ['6', '17'])).
% 2.03/2.23  thf('62', plain,
% 2.03/2.23      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.03/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.23  thf('63', plain,
% 2.03/2.23      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.03/2.23         (~ (m1_pre_topc @ X18 @ X19)
% 2.03/2.23          | ~ (r1_tarski @ X20 @ (k2_struct_0 @ X18))
% 2.03/2.23          | ((sk_D @ X20 @ X18) = (X20))
% 2.03/2.23          | (v2_compts_1 @ X20 @ X19)
% 2.03/2.23          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 2.03/2.23          | ~ (l1_pre_topc @ X19))),
% 2.03/2.23      inference('cnf', [status(esa)], [t11_compts_1])).
% 2.03/2.23  thf('64', plain,
% 2.03/2.23      (![X0 : $i]:
% 2.03/2.23         (~ (l1_pre_topc @ sk_A)
% 2.03/2.23          | (v2_compts_1 @ sk_B @ sk_A)
% 2.03/2.23          | ((sk_D @ sk_B @ X0) = (sk_B))
% 2.03/2.23          | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 2.03/2.23          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 2.03/2.23      inference('sup-', [status(thm)], ['62', '63'])).
% 2.03/2.23  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 2.03/2.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.03/2.23  thf('66', plain,
% 2.03/2.23      (![X0 : $i]:
% 2.03/2.23         ((v2_compts_1 @ sk_B @ sk_A)
% 2.03/2.23          | ((sk_D @ sk_B @ X0) = (sk_B))
% 2.03/2.23          | ~ (r1_tarski @ sk_B @ (k2_struct_0 @ X0))
% 2.03/2.23          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 2.03/2.23      inference('demod', [status(thm)], ['64', '65'])).
% 2.03/2.23  thf('67', plain,
% 2.03/2.23      ((~ (r1_tarski @ sk_B @ sk_B)
% 2.03/2.23        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 2.03/2.23        | ((sk_D @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 2.03/2.23        | (v2_compts_1 @ sk_B @ sk_A))),
% 2.03/2.23      inference('sup-', [status(thm)], ['61', '66'])).
% 2.03/2.23  thf('68', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.03/2.23      inference('simplify', [status(thm)], ['25'])).
% 2.03/2.23  thf('69', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 2.03/2.23      inference('demod', [status(thm)], ['9', '10'])).
% 2.03/2.23  thf('70', plain,
% 2.03/2.23      ((((sk_D @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 2.03/2.23        | (v2_compts_1 @ sk_B @ sk_A))),
% 2.03/2.23      inference('demod', [status(thm)], ['67', '68', '69'])).
% 2.03/2.23  thf('71', plain, (~ (v2_compts_1 @ sk_B @ sk_A)),
% 2.03/2.23      inference('simpl_trail', [status(thm)], ['30', '58'])).
% 2.03/2.23  thf('72', plain, (((sk_D @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 2.03/2.23      inference('clc', [status(thm)], ['70', '71'])).
% 2.03/2.23  thf('73', plain,
% 2.03/2.23      (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))
% 2.03/2.23         <= (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))),
% 2.03/2.23      inference('split', [status(esa)], ['33'])).
% 2.03/2.23  thf('74', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 2.03/2.23      inference('demod', [status(thm)], ['6', '17'])).
% 2.03/2.23  thf('75', plain,
% 2.03/2.23      (![X17 : $i]:
% 2.03/2.23         (~ (v1_compts_1 @ X17)
% 2.03/2.23          | (v2_compts_1 @ (k2_struct_0 @ X17) @ X17)
% 2.03/2.23          | ~ (l1_pre_topc @ X17))),
% 2.03/2.23      inference('cnf', [status(esa)], [t10_compts_1])).
% 2.03/2.23  thf('76', plain,
% 2.03/2.23      (((v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))
% 2.03/2.23        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 2.03/2.23        | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 2.03/2.23      inference('sup+', [status(thm)], ['74', '75'])).
% 2.03/2.23  thf('77', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 2.03/2.23      inference('demod', [status(thm)], ['13', '14'])).
% 2.03/2.23  thf('78', plain,
% 2.03/2.23      (((v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))
% 2.03/2.23        | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 2.03/2.23      inference('demod', [status(thm)], ['76', '77'])).
% 2.03/2.23  thf('79', plain,
% 2.03/2.23      (((v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B)))
% 2.03/2.23         <= (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))),
% 2.03/2.23      inference('sup-', [status(thm)], ['73', '78'])).
% 2.03/2.23  thf('80', plain,
% 2.03/2.23      (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))) | 
% 2.03/2.23       ((v2_compts_1 @ sk_B @ sk_A))),
% 2.03/2.23      inference('split', [status(esa)], ['33'])).
% 2.03/2.23  thf('81', plain, (((v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 2.03/2.23      inference('sat_resolution*', [status(thm)], ['31', '57', '80'])).
% 2.03/2.23  thf('82', plain, ((v2_compts_1 @ sk_B @ (k1_pre_topc @ sk_A @ sk_B))),
% 2.03/2.23      inference('simpl_trail', [status(thm)], ['79', '81'])).
% 2.03/2.23  thf('83', plain, ($false),
% 2.03/2.23      inference('demod', [status(thm)], ['60', '72', '82'])).
% 2.03/2.23  
% 2.03/2.23  % SZS output end Refutation
% 2.03/2.23  
% 2.03/2.24  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
