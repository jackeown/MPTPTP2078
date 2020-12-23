%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.P38OsLkXUc

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:05 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 246 expanded)
%              Number of leaves         :   20 (  82 expanded)
%              Depth                    :   13
%              Number of atoms          :  669 (2708 expanded)
%              Number of equality atoms :   31 (  64 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t79_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v1_tops_1 @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( v1_tops_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v1_tops_1 @ B @ A )
                    & ( r1_tarski @ B @ C ) )
                 => ( v1_tops_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t79_tops_1])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('12',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('18',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v1_tops_1 @ X13 @ X14 )
      | ( ( k2_pre_topc @ X14 @ X13 )
        = ( k2_struct_0 @ X14 ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('32',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','30','31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('37',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','35','36'])).

thf('38',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['14','37'])).

thf('39',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('45',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( k2_pre_topc @ X14 @ X13 )
       != ( k2_struct_0 @ X14 ) )
      | ( v1_tops_1 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ X1 @ X0 )
      | ( ( k2_pre_topc @ X0 @ X1 )
       != ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ( v1_tops_1 @ sk_C @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('50',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ( v1_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ~ ( v1_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ( k2_pre_topc @ sk_A @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['38','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('55',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t49_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('61',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( r1_tarski @ X10 @ X12 )
      | ( r1_tarski @ ( k2_pre_topc @ X11 @ X10 ) @ ( k2_pre_topc @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ X1 ) @ ( k2_pre_topc @ X0 @ X2 ) )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('65',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','35','36'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('69',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) )
    | ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['54','68'])).

thf('70',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['53','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.P38OsLkXUc
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:27:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 215 iterations in 0.103s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.55  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.36/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.55  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.36/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.36/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.55  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.36/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.55  thf(d3_struct_0, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.36/0.55  thf('0', plain,
% 0.36/0.55      (![X6 : $i]:
% 0.36/0.55         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.36/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.55  thf(t79_tops_1, conjecture,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55           ( ![C:$i]:
% 0.36/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55               ( ( ( v1_tops_1 @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.36/0.55                 ( v1_tops_1 @ C @ A ) ) ) ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i]:
% 0.36/0.55        ( ( l1_pre_topc @ A ) =>
% 0.36/0.55          ( ![B:$i]:
% 0.36/0.55            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55              ( ![C:$i]:
% 0.36/0.55                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55                  ( ( ( v1_tops_1 @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.36/0.55                    ( v1_tops_1 @ C @ A ) ) ) ) ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t79_tops_1])).
% 0.36/0.55  thf('1', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(dt_k2_pre_topc, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( l1_pre_topc @ A ) & 
% 0.36/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.36/0.55       ( m1_subset_1 @
% 0.36/0.55         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.36/0.55  thf('2', plain,
% 0.36/0.55      (![X7 : $i, X8 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ X7)
% 0.36/0.55          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.36/0.55          | (m1_subset_1 @ (k2_pre_topc @ X7 @ X8) @ 
% 0.36/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.36/0.55  thf('3', plain,
% 0.36/0.55      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.36/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.55  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('5', plain,
% 0.36/0.55      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.36/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('demod', [status(thm)], ['3', '4'])).
% 0.36/0.55  thf(t3_subset, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      (![X3 : $i, X4 : $i]:
% 0.36/0.55         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.36/0.55  thf(d10_xboole_0, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.55  thf('8', plain,
% 0.36/0.55      (![X0 : $i, X2 : $i]:
% 0.36/0.55         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.36/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      ((~ (r1_tarski @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_C))
% 0.36/0.55        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_C)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.55  thf('10', plain,
% 0.36/0.55      ((~ (r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_C))
% 0.36/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.36/0.55        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_C)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['0', '9'])).
% 0.36/0.55  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(dt_l1_pre_topc, axiom,
% 0.36/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.36/0.55  thf('12', plain, (![X9 : $i]: ((l1_struct_0 @ X9) | ~ (l1_pre_topc @ X9))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.36/0.55  thf('13', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.55  thf('14', plain,
% 0.36/0.55      ((~ (r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_C))
% 0.36/0.55        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_C)))),
% 0.36/0.55      inference('demod', [status(thm)], ['10', '13'])).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      (![X6 : $i]:
% 0.36/0.55         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.36/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.55  thf('16', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('17', plain,
% 0.36/0.55      (![X7 : $i, X8 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ X7)
% 0.36/0.55          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.36/0.55          | (m1_subset_1 @ (k2_pre_topc @ X7 @ X8) @ 
% 0.36/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.36/0.55  thf('18', plain,
% 0.36/0.55      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.36/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.55  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('20', plain,
% 0.36/0.55      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.36/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('demod', [status(thm)], ['18', '19'])).
% 0.36/0.55  thf('21', plain,
% 0.36/0.55      (![X3 : $i, X4 : $i]:
% 0.36/0.55         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.36/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.55  thf('22', plain,
% 0.36/0.55      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      (![X0 : $i, X2 : $i]:
% 0.36/0.55         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.36/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.55  thf('24', plain,
% 0.36/0.55      ((~ (r1_tarski @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 0.36/0.55        | ((u1_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_B)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.55  thf('25', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(d3_tops_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55           ( ( v1_tops_1 @ B @ A ) <=>
% 0.36/0.55             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.36/0.55  thf('26', plain,
% 0.36/0.55      (![X13 : $i, X14 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.36/0.55          | ~ (v1_tops_1 @ X13 @ X14)
% 0.36/0.55          | ((k2_pre_topc @ X14 @ X13) = (k2_struct_0 @ X14))
% 0.36/0.55          | ~ (l1_pre_topc @ X14))),
% 0.36/0.55      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.36/0.55  thf('27', plain,
% 0.36/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.55        | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 0.36/0.55        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.36/0.55  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('29', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('30', plain, (((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.36/0.55  thf('31', plain, (((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.36/0.55  thf('32', plain,
% 0.36/0.55      ((~ (r1_tarski @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.36/0.55        | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))),
% 0.36/0.55      inference('demod', [status(thm)], ['24', '30', '31'])).
% 0.36/0.55  thf('33', plain,
% 0.36/0.55      ((~ (r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.36/0.55        | ~ (l1_struct_0 @ sk_A)
% 0.36/0.55        | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['15', '32'])).
% 0.36/0.55  thf('34', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.55  thf('35', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.36/0.55      inference('simplify', [status(thm)], ['34'])).
% 0.36/0.55  thf('36', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.55  thf('37', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['33', '35', '36'])).
% 0.36/0.55  thf('38', plain,
% 0.36/0.55      ((~ (r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_C))
% 0.36/0.55        | ((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_C)))),
% 0.36/0.55      inference('demod', [status(thm)], ['14', '37'])).
% 0.36/0.55  thf('39', plain,
% 0.36/0.55      (![X6 : $i]:
% 0.36/0.55         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.36/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.55  thf('40', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('41', plain,
% 0.36/0.55      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.36/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.55      inference('sup+', [status(thm)], ['39', '40'])).
% 0.36/0.55  thf('42', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.55  thf('43', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.36/0.55      inference('demod', [status(thm)], ['41', '42'])).
% 0.36/0.55  thf('44', plain,
% 0.36/0.55      (![X6 : $i]:
% 0.36/0.55         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.36/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.55  thf('45', plain,
% 0.36/0.55      (![X13 : $i, X14 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.36/0.55          | ((k2_pre_topc @ X14 @ X13) != (k2_struct_0 @ X14))
% 0.36/0.55          | (v1_tops_1 @ X13 @ X14)
% 0.36/0.55          | ~ (l1_pre_topc @ X14))),
% 0.36/0.55      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.36/0.55  thf('46', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.36/0.55          | ~ (l1_struct_0 @ X0)
% 0.36/0.55          | ~ (l1_pre_topc @ X0)
% 0.36/0.55          | (v1_tops_1 @ X1 @ X0)
% 0.36/0.55          | ((k2_pre_topc @ X0 @ X1) != (k2_struct_0 @ X0)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.36/0.55  thf('47', plain,
% 0.36/0.55      ((((k2_pre_topc @ sk_A @ sk_C) != (k2_struct_0 @ sk_A))
% 0.36/0.55        | (v1_tops_1 @ sk_C @ sk_A)
% 0.36/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['43', '46'])).
% 0.36/0.55  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('49', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.55  thf('50', plain,
% 0.36/0.55      ((((k2_pre_topc @ sk_A @ sk_C) != (k2_struct_0 @ sk_A))
% 0.36/0.55        | (v1_tops_1 @ sk_C @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.36/0.55  thf('51', plain, (~ (v1_tops_1 @ sk_C @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('52', plain, (((k2_pre_topc @ sk_A @ sk_C) != (k2_struct_0 @ sk_A))),
% 0.36/0.55      inference('clc', [status(thm)], ['50', '51'])).
% 0.36/0.55  thf('53', plain,
% 0.36/0.55      (~ (r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_C))),
% 0.36/0.55      inference('simplify_reflect-', [status(thm)], ['38', '52'])).
% 0.36/0.55  thf('54', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.36/0.55      inference('demod', [status(thm)], ['41', '42'])).
% 0.36/0.55  thf('55', plain,
% 0.36/0.55      (![X6 : $i]:
% 0.36/0.55         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.36/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.55  thf('56', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('57', plain,
% 0.36/0.55      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.36/0.55        | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.55      inference('sup+', [status(thm)], ['55', '56'])).
% 0.36/0.55  thf('58', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.55  thf('59', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.36/0.55      inference('demod', [status(thm)], ['57', '58'])).
% 0.36/0.55  thf('60', plain,
% 0.36/0.55      (![X6 : $i]:
% 0.36/0.55         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.36/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.36/0.55  thf(t49_pre_topc, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55           ( ![C:$i]:
% 0.36/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55               ( ( r1_tarski @ B @ C ) =>
% 0.36/0.55                 ( r1_tarski @
% 0.36/0.55                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf('61', plain,
% 0.36/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.36/0.55          | ~ (r1_tarski @ X10 @ X12)
% 0.36/0.55          | (r1_tarski @ (k2_pre_topc @ X11 @ X10) @ (k2_pre_topc @ X11 @ X12))
% 0.36/0.55          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.36/0.55          | ~ (l1_pre_topc @ X11))),
% 0.36/0.55      inference('cnf', [status(esa)], [t49_pre_topc])).
% 0.36/0.55  thf('62', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.36/0.55          | ~ (l1_struct_0 @ X0)
% 0.36/0.55          | ~ (l1_pre_topc @ X0)
% 0.36/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.36/0.55          | (r1_tarski @ (k2_pre_topc @ X0 @ X1) @ (k2_pre_topc @ X0 @ X2))
% 0.36/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.36/0.55      inference('sup-', [status(thm)], ['60', '61'])).
% 0.36/0.55  thf('63', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (r1_tarski @ sk_B @ X0)
% 0.36/0.55          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.36/0.55             (k2_pre_topc @ sk_A @ X0))
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.36/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.36/0.55          | ~ (l1_struct_0 @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['59', '62'])).
% 0.36/0.55  thf('64', plain, (((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.36/0.55  thf('65', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['33', '35', '36'])).
% 0.36/0.55  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('67', plain, ((l1_struct_0 @ sk_A)),
% 0.36/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.55  thf('68', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (r1_tarski @ sk_B @ X0)
% 0.36/0.55          | (r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ X0))
% 0.36/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 0.36/0.55      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 0.36/0.55  thf('69', plain,
% 0.36/0.55      (((r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_C))
% 0.36/0.55        | ~ (r1_tarski @ sk_B @ sk_C))),
% 0.36/0.55      inference('sup-', [status(thm)], ['54', '68'])).
% 0.36/0.55  thf('70', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('71', plain,
% 0.36/0.55      ((r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_C))),
% 0.36/0.55      inference('demod', [status(thm)], ['69', '70'])).
% 0.36/0.55  thf('72', plain, ($false), inference('demod', [status(thm)], ['53', '71'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
