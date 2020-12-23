%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jGU2Fc3crD

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 310 expanded)
%              Number of leaves         :   22 ( 102 expanded)
%              Depth                    :   17
%              Number of atoms          :  692 (2910 expanded)
%              Number of equality atoms :   36 (  88 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
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

thf('2',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('4',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_pre_topc @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X8 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_pre_topc @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    r1_tarski @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('16',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('22',plain,
    ( ( k2_xboole_0 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_xboole_0 @ sk_C @ ( k2_struct_0 @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['17','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('25',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf('27',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('28',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11','26','27'])).

thf('29',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('32',plain,
    ( ( k2_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('34',plain,
    ( ( k2_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('36',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf(t49_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('42',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( r1_tarski @ X11 @ X13 )
      | ( r1_tarski @ ( k2_pre_topc @ X12 @ X11 ) @ ( k2_pre_topc @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ ( k2_pre_topc @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('49',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['16','25'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('50',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v1_tops_1 @ X14 @ X15 )
      | ( ( k2_pre_topc @ X15 @ X14 )
        = ( k2_struct_0 @ X15 ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ X0 )
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_tops_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ X0 )
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_tops_1 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( v1_tops_1 @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['47','56'])).

thf('58',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) )
    | ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['35','57'])).

thf('59',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('62',plain,
    ( ( k2_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_C ) )
    = ( k2_pre_topc @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_pre_topc @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['34','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('65',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('66',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k2_pre_topc @ X15 @ X14 )
       != ( k2_struct_0 @ X15 ) )
      | ( v1_tops_1 @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ X1 @ X0 )
      | ( ( k2_pre_topc @ X0 @ X1 )
       != ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ( v1_tops_1 @ sk_C @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('71',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ( v1_tops_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    ~ ( v1_tops_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ( k2_pre_topc @ sk_A @ sk_C )
 != ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['63','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jGU2Fc3crD
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:05:12 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 118 iterations in 0.033s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.51  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.21/0.51  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(d3_struct_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (![X7 : $i]:
% 0.21/0.51         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.51  thf(t79_tops_1, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51               ( ( ( v1_tops_1 @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.51                 ( v1_tops_1 @ C @ A ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( l1_pre_topc @ A ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51              ( ![C:$i]:
% 0.21/0.51                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51                  ( ( ( v1_tops_1 @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.51                    ( v1_tops_1 @ C @ A ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t79_tops_1])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.21/0.52        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.52  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_l1_pre_topc, axiom,
% 0.21/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.52  thf('4', plain, (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.52  thf('5', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['2', '5'])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X7 : $i]:
% 0.21/0.52         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.52  thf(dt_k2_pre_topc, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( l1_pre_topc @ A ) & 
% 0.21/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.52       ( m1_subset_1 @
% 0.21/0.52         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X8)
% 0.21/0.52          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.21/0.52          | (m1_subset_1 @ (k2_pre_topc @ X8 @ X9) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X8))))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.21/0.52          | ~ (l1_struct_0 @ X0)
% 0.21/0.52          | (m1_subset_1 @ (k2_pre_topc @ X0 @ X1) @ 
% 0.21/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.52          | ~ (l1_pre_topc @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | (m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.21/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.52  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['2', '5'])).
% 0.21/0.52  thf(t3_subset, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i]:
% 0.21/0.52         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.52  thf('14', plain, ((r1_tarski @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf(t12_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X2 : $i, X3 : $i]:
% 0.21/0.52         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (((k2_xboole_0 @ sk_C @ (k2_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X7 : $i]:
% 0.21/0.52         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i]:
% 0.21/0.52         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.52  thf('20', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X2 : $i, X3 : $i]:
% 0.21/0.52         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (((k2_xboole_0 @ sk_C @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      ((((k2_xboole_0 @ sk_C @ (k2_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))
% 0.21/0.52        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup+', [status(thm)], ['17', '22'])).
% 0.21/0.52  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (((k2_xboole_0 @ sk_C @ (k2_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf('26', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup+', [status(thm)], ['16', '25'])).
% 0.21/0.52  thf('27', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_C) @ 
% 0.21/0.52        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['10', '11', '26', '27'])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i]:
% 0.21/0.52         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_C) @ (k2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (![X2 : $i, X3 : $i]:
% 0.21/0.52         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (((k2_xboole_0 @ (k2_pre_topc @ sk_A @ sk_C) @ (k2_struct_0 @ sk_A))
% 0.21/0.52         = (k2_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.52  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (((k2_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_C))
% 0.21/0.52         = (k2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['2', '5'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (![X7 : $i]:
% 0.21/0.52         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.21/0.52        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup+', [status(thm)], ['36', '37'])).
% 0.21/0.52  thf('39', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.52  thf('41', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup+', [status(thm)], ['16', '25'])).
% 0.21/0.52  thf(t49_pre_topc, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52               ( ( r1_tarski @ B @ C ) =>
% 0.21/0.52                 ( r1_tarski @
% 0.21/0.52                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.52          | ~ (r1_tarski @ X11 @ X13)
% 0.21/0.52          | (r1_tarski @ (k2_pre_topc @ X12 @ X11) @ (k2_pre_topc @ X12 @ X13))
% 0.21/0.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.52          | ~ (l1_pre_topc @ X12))),
% 0.21/0.52      inference('cnf', [status(esa)], [t49_pre_topc])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.21/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.52          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ (k2_pre_topc @ sk_A @ X1))
% 0.21/0.52          | ~ (r1_tarski @ X0 @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.52  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('45', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup+', [status(thm)], ['16', '25'])).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.21/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.21/0.52          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ (k2_pre_topc @ sk_A @ X1))
% 0.21/0.52          | ~ (r1_tarski @ X0 @ X1))),
% 0.21/0.52      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (r1_tarski @ sk_B @ X0)
% 0.21/0.52          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.52             (k2_pre_topc @ sk_A @ X0))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['40', '46'])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.52  thf('49', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup+', [status(thm)], ['16', '25'])).
% 0.21/0.52  thf(d3_tops_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.52           ( ( v1_tops_1 @ B @ A ) <=>
% 0.21/0.52             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.52          | ~ (v1_tops_1 @ X14 @ X15)
% 0.21/0.52          | ((k2_pre_topc @ X15 @ X14) = (k2_struct_0 @ X15))
% 0.21/0.52          | ~ (l1_pre_topc @ X15))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.21/0.52          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52          | ((k2_pre_topc @ sk_A @ X0) = (k2_struct_0 @ sk_A))
% 0.21/0.52          | ~ (v1_tops_1 @ X0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.52  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.21/0.52          | ((k2_pre_topc @ sk_A @ X0) = (k2_struct_0 @ sk_A))
% 0.21/0.52          | ~ (v1_tops_1 @ X0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      ((~ (v1_tops_1 @ sk_B @ sk_A)
% 0.21/0.52        | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['48', '53'])).
% 0.21/0.52  thf('55', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('56', plain, (((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.52  thf('57', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (r1_tarski @ sk_B @ X0)
% 0.21/0.52          | (r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ X0))
% 0.21/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))),
% 0.21/0.52      inference('demod', [status(thm)], ['47', '56'])).
% 0.21/0.52  thf('58', plain,
% 0.21/0.52      (((r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_C))
% 0.21/0.52        | ~ (r1_tarski @ sk_B @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['35', '57'])).
% 0.21/0.52  thf('59', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('60', plain,
% 0.21/0.52      ((r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_C))),
% 0.21/0.52      inference('demod', [status(thm)], ['58', '59'])).
% 0.21/0.52  thf('61', plain,
% 0.21/0.52      (![X2 : $i, X3 : $i]:
% 0.21/0.52         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.21/0.52      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.52  thf('62', plain,
% 0.21/0.52      (((k2_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_C))
% 0.21/0.52         = (k2_pre_topc @ sk_A @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.52  thf('63', plain, (((k2_struct_0 @ sk_A) = (k2_pre_topc @ sk_A @ sk_C))),
% 0.21/0.52      inference('sup+', [status(thm)], ['34', '62'])).
% 0.21/0.52  thf('64', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.21/0.52      inference('demod', [status(thm)], ['2', '5'])).
% 0.21/0.52  thf('65', plain,
% 0.21/0.52      (![X7 : $i]:
% 0.21/0.52         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.52  thf('66', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.21/0.52          | ((k2_pre_topc @ X15 @ X14) != (k2_struct_0 @ X15))
% 0.21/0.52          | (v1_tops_1 @ X14 @ X15)
% 0.21/0.52          | ~ (l1_pre_topc @ X15))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.21/0.52  thf('67', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.21/0.52          | ~ (l1_struct_0 @ X0)
% 0.21/0.52          | ~ (l1_pre_topc @ X0)
% 0.21/0.52          | (v1_tops_1 @ X1 @ X0)
% 0.21/0.52          | ((k2_pre_topc @ X0 @ X1) != (k2_struct_0 @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.52  thf('68', plain,
% 0.21/0.52      ((((k2_pre_topc @ sk_A @ sk_C) != (k2_struct_0 @ sk_A))
% 0.21/0.52        | (v1_tops_1 @ sk_C @ sk_A)
% 0.21/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.52        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.52      inference('sup-', [status(thm)], ['64', '67'])).
% 0.21/0.52  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('70', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf('71', plain,
% 0.21/0.52      ((((k2_pre_topc @ sk_A @ sk_C) != (k2_struct_0 @ sk_A))
% 0.21/0.52        | (v1_tops_1 @ sk_C @ sk_A))),
% 0.21/0.52      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.21/0.52  thf('72', plain, (~ (v1_tops_1 @ sk_C @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('73', plain, (((k2_pre_topc @ sk_A @ sk_C) != (k2_struct_0 @ sk_A))),
% 0.21/0.52      inference('clc', [status(thm)], ['71', '72'])).
% 0.21/0.52  thf('74', plain, ($false),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['63', '73'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
