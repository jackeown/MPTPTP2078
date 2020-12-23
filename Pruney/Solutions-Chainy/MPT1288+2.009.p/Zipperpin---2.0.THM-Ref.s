%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uptX0fOsKI

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:59 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 283 expanded)
%              Number of leaves         :   33 (  93 expanded)
%              Depth                    :   16
%              Number of atoms          : 1320 (3608 expanded)
%              Number of equality atoms :   37 ( 140 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_tops_1_type,type,(
    v4_tops_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t110_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_tops_1 @ B @ A )
           => ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) )
              = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_tops_1 @ B @ A )
             => ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) )
                = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t110_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('2',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l80_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) )
            = k1_xboole_0 ) ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( ( k1_tops_1 @ X23 @ ( k2_tops_1 @ X23 @ ( k2_tops_1 @ X23 @ X22 ) ) )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[l80_tops_1])).

thf('6',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t94_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( ( v3_tops_1 @ B @ A )
            <=> ( B
                = ( k2_tops_1 @ A @ B ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_tops_1 @ X28 @ X29 )
      | ( X28
        = ( k2_tops_1 @ X29 @ X28 ) )
      | ~ ( v4_pre_topc @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t94_tops_1])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) )
    | ~ ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(fc11_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_tops_1 @ A @ B ) @ A ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v4_pre_topc @ ( k2_tops_1 @ X16 @ X17 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc11_tops_1])).

thf('21',plain,
    ( ( v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v4_pre_topc @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t95_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
           => ( v3_tops_1 @ ( k2_tops_1 @ A @ B ) @ A ) ) ) ) )).

thf('26',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( v3_tops_1 @ ( k2_tops_1 @ X31 @ X30 ) @ X31 )
      | ~ ( v3_pre_topc @ X30 @ X31 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t95_tops_1])).

thf('27',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ( v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X18 @ X19 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('32',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    v3_tops_1 @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['27','28','29','35'])).

thf('37',plain,
    ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','24','36'])).

thf('38',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['9','37'])).

thf('39',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('40',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k2_tops_1 @ X21 @ X20 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X21 ) @ ( k2_pre_topc @ X21 @ X20 ) @ ( k1_tops_1 @ X21 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('45',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X3 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('46',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('50',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( r1_tarski @ X7 @ X9 )
      | ( r1_tarski @ ( k2_pre_topc @ X8 @ X7 ) @ ( k2_pre_topc @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_tops_1 @ B @ A )
          <=> ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B )
              & ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )).

thf('56',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v4_tops_1 @ X10 @ X11 )
      | ( r1_tarski @ X10 @ ( k2_pre_topc @ X11 @ ( k1_tops_1 @ X11 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d6_tops_1])).

thf('57',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v4_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('62',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( ( k2_pre_topc @ X5 @ ( k2_pre_topc @ X5 @ X6 ) )
        = ( k2_pre_topc @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('63',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','60','65'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('67',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('68',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    | ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('71',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('72',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( r1_tarski @ X7 @ X9 )
      | ( r1_tarski @ ( k2_pre_topc @ X8 @ X7 ) @ ( k2_pre_topc @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('80',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( k1_tops_1 @ X24 @ ( k1_tops_1 @ X24 @ X25 ) )
        = ( k1_tops_1 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('81',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['78','83','84'])).

thf('86',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('88',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X27 @ X26 ) @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('89',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['86','91'])).

thf('93',plain,
    ( ( k2_pre_topc @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['68','92'])).

thf('94',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('95',plain,
    ( ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k2_tops_1 @ X21 @ X20 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X21 ) @ ( k2_pre_topc @ X21 @ X20 ) @ ( k1_tops_1 @ X21 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('98',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k2_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['95','100'])).

thf('102',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['38','101'])).

thf('103',plain,(
    ( k1_tops_1 @ sk_A @ ( k2_tops_1 @ sk_A @ sk_B ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['102','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uptX0fOsKI
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:05:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.36  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.99/1.19  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.99/1.19  % Solved by: fo/fo7.sh
% 0.99/1.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.19  % done 1243 iterations in 0.743s
% 0.99/1.19  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.99/1.19  % SZS output start Refutation
% 0.99/1.19  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.99/1.19  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.99/1.19  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.99/1.19  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.99/1.19  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.99/1.19  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.99/1.19  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.99/1.19  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.99/1.19  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.99/1.19  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.99/1.19  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.99/1.19  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.99/1.19  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.19  thf(v4_tops_1_type, type, v4_tops_1: $i > $i > $o).
% 0.99/1.19  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.99/1.19  thf(sk_B_type, type, sk_B: $i).
% 0.99/1.19  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.99/1.19  thf(t110_tops_1, conjecture,
% 0.99/1.19    (![A:$i]:
% 0.99/1.19     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.99/1.19       ( ![B:$i]:
% 0.99/1.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.19           ( ( v4_tops_1 @ B @ A ) =>
% 0.99/1.19             ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.99/1.19  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.19    (~( ![A:$i]:
% 0.99/1.19        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.99/1.19          ( ![B:$i]:
% 0.99/1.19            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.19              ( ( v4_tops_1 @ B @ A ) =>
% 0.99/1.19                ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.99/1.19    inference('cnf.neg', [status(esa)], [t110_tops_1])).
% 0.99/1.19  thf('0', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf(dt_k1_tops_1, axiom,
% 0.99/1.19    (![A:$i,B:$i]:
% 0.99/1.19     ( ( ( l1_pre_topc @ A ) & 
% 0.99/1.19         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.19       ( m1_subset_1 @
% 0.99/1.19         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.99/1.19  thf('1', plain,
% 0.99/1.19      (![X12 : $i, X13 : $i]:
% 0.99/1.19         (~ (l1_pre_topc @ X12)
% 0.99/1.19          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.99/1.19          | (m1_subset_1 @ (k1_tops_1 @ X12 @ X13) @ 
% 0.99/1.19             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.99/1.19      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.99/1.19  thf('2', plain,
% 0.99/1.19      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.19         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.99/1.19        | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.19      inference('sup-', [status(thm)], ['0', '1'])).
% 0.99/1.19  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('4', plain,
% 0.99/1.19      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.19        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('demod', [status(thm)], ['2', '3'])).
% 0.99/1.19  thf(l80_tops_1, axiom,
% 0.99/1.19    (![A:$i]:
% 0.99/1.19     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.99/1.19       ( ![B:$i]:
% 0.99/1.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.19           ( ( k1_tops_1 @ A @ ( k2_tops_1 @ A @ ( k2_tops_1 @ A @ B ) ) ) =
% 0.99/1.19             ( k1_xboole_0 ) ) ) ) ))).
% 0.99/1.19  thf('5', plain,
% 0.99/1.19      (![X22 : $i, X23 : $i]:
% 0.99/1.19         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.99/1.19          | ((k1_tops_1 @ X23 @ (k2_tops_1 @ X23 @ (k2_tops_1 @ X23 @ X22)))
% 0.99/1.19              = (k1_xboole_0))
% 0.99/1.19          | ~ (l1_pre_topc @ X23)
% 0.99/1.19          | ~ (v2_pre_topc @ X23))),
% 0.99/1.19      inference('cnf', [status(esa)], [l80_tops_1])).
% 0.99/1.19  thf('6', plain,
% 0.99/1.19      ((~ (v2_pre_topc @ sk_A)
% 0.99/1.19        | ~ (l1_pre_topc @ sk_A)
% 0.99/1.19        | ((k1_tops_1 @ sk_A @ 
% 0.99/1.19            (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.99/1.19            = (k1_xboole_0)))),
% 0.99/1.19      inference('sup-', [status(thm)], ['4', '5'])).
% 0.99/1.19  thf('7', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('9', plain,
% 0.99/1.19      (((k1_tops_1 @ sk_A @ 
% 0.99/1.19         (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.99/1.19         = (k1_xboole_0))),
% 0.99/1.19      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.99/1.19  thf('10', plain,
% 0.99/1.19      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.19        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('demod', [status(thm)], ['2', '3'])).
% 0.99/1.19  thf(dt_k2_tops_1, axiom,
% 0.99/1.19    (![A:$i,B:$i]:
% 0.99/1.19     ( ( ( l1_pre_topc @ A ) & 
% 0.99/1.19         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.19       ( m1_subset_1 @
% 0.99/1.19         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.99/1.19  thf('11', plain,
% 0.99/1.19      (![X14 : $i, X15 : $i]:
% 0.99/1.19         (~ (l1_pre_topc @ X14)
% 0.99/1.19          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.99/1.19          | (m1_subset_1 @ (k2_tops_1 @ X14 @ X15) @ 
% 0.99/1.19             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.99/1.19      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 0.99/1.19  thf('12', plain,
% 0.99/1.19      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.99/1.19         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.99/1.19        | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.19      inference('sup-', [status(thm)], ['10', '11'])).
% 0.99/1.19  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('14', plain,
% 0.99/1.19      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.99/1.19        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('demod', [status(thm)], ['12', '13'])).
% 0.99/1.19  thf(t94_tops_1, axiom,
% 0.99/1.19    (![A:$i]:
% 0.99/1.19     ( ( l1_pre_topc @ A ) =>
% 0.99/1.19       ( ![B:$i]:
% 0.99/1.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.19           ( ( v4_pre_topc @ B @ A ) =>
% 0.99/1.19             ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 0.99/1.19  thf('15', plain,
% 0.99/1.19      (![X28 : $i, X29 : $i]:
% 0.99/1.19         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.99/1.19          | ~ (v3_tops_1 @ X28 @ X29)
% 0.99/1.19          | ((X28) = (k2_tops_1 @ X29 @ X28))
% 0.99/1.19          | ~ (v4_pre_topc @ X28 @ X29)
% 0.99/1.19          | ~ (l1_pre_topc @ X29))),
% 0.99/1.19      inference('cnf', [status(esa)], [t94_tops_1])).
% 0.99/1.19  thf('16', plain,
% 0.99/1.19      ((~ (l1_pre_topc @ sk_A)
% 0.99/1.19        | ~ (v4_pre_topc @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.99/1.19             sk_A)
% 0.99/1.19        | ((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.99/1.19            = (k2_tops_1 @ sk_A @ 
% 0.99/1.19               (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.99/1.19        | ~ (v3_tops_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A))),
% 0.99/1.19      inference('sup-', [status(thm)], ['14', '15'])).
% 0.99/1.19  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('18', plain,
% 0.99/1.19      ((~ (v4_pre_topc @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)
% 0.99/1.19        | ((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.99/1.19            = (k2_tops_1 @ sk_A @ 
% 0.99/1.19               (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.99/1.19        | ~ (v3_tops_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A))),
% 0.99/1.19      inference('demod', [status(thm)], ['16', '17'])).
% 0.99/1.19  thf('19', plain,
% 0.99/1.19      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.19        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('demod', [status(thm)], ['2', '3'])).
% 0.99/1.19  thf(fc11_tops_1, axiom,
% 0.99/1.19    (![A:$i,B:$i]:
% 0.99/1.19     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.99/1.19         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.19       ( v4_pre_topc @ ( k2_tops_1 @ A @ B ) @ A ) ))).
% 0.99/1.19  thf('20', plain,
% 0.99/1.19      (![X16 : $i, X17 : $i]:
% 0.99/1.19         (~ (l1_pre_topc @ X16)
% 0.99/1.19          | ~ (v2_pre_topc @ X16)
% 0.99/1.19          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.99/1.19          | (v4_pre_topc @ (k2_tops_1 @ X16 @ X17) @ X16))),
% 0.99/1.19      inference('cnf', [status(esa)], [fc11_tops_1])).
% 0.99/1.19  thf('21', plain,
% 0.99/1.19      (((v4_pre_topc @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)
% 0.99/1.19        | ~ (v2_pre_topc @ sk_A)
% 0.99/1.19        | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.19      inference('sup-', [status(thm)], ['19', '20'])).
% 0.99/1.19  thf('22', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('24', plain,
% 0.99/1.19      ((v4_pre_topc @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)),
% 0.99/1.19      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.99/1.19  thf('25', plain,
% 0.99/1.19      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.19        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('demod', [status(thm)], ['2', '3'])).
% 0.99/1.19  thf(t95_tops_1, axiom,
% 0.99/1.19    (![A:$i]:
% 0.99/1.19     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.99/1.19       ( ![B:$i]:
% 0.99/1.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.19           ( ( v3_pre_topc @ B @ A ) =>
% 0.99/1.19             ( v3_tops_1 @ ( k2_tops_1 @ A @ B ) @ A ) ) ) ) ))).
% 0.99/1.19  thf('26', plain,
% 0.99/1.19      (![X30 : $i, X31 : $i]:
% 0.99/1.19         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.99/1.19          | (v3_tops_1 @ (k2_tops_1 @ X31 @ X30) @ X31)
% 0.99/1.19          | ~ (v3_pre_topc @ X30 @ X31)
% 0.99/1.19          | ~ (l1_pre_topc @ X31)
% 0.99/1.19          | ~ (v2_pre_topc @ X31))),
% 0.99/1.19      inference('cnf', [status(esa)], [t95_tops_1])).
% 0.99/1.19  thf('27', plain,
% 0.99/1.19      ((~ (v2_pre_topc @ sk_A)
% 0.99/1.19        | ~ (l1_pre_topc @ sk_A)
% 0.99/1.19        | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.99/1.19        | (v3_tops_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A))),
% 0.99/1.19      inference('sup-', [status(thm)], ['25', '26'])).
% 0.99/1.19  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('30', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf(fc9_tops_1, axiom,
% 0.99/1.19    (![A:$i,B:$i]:
% 0.99/1.19     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.99/1.19         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.19       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.99/1.19  thf('31', plain,
% 0.99/1.19      (![X18 : $i, X19 : $i]:
% 0.99/1.19         (~ (l1_pre_topc @ X18)
% 0.99/1.19          | ~ (v2_pre_topc @ X18)
% 0.99/1.19          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.99/1.19          | (v3_pre_topc @ (k1_tops_1 @ X18 @ X19) @ X18))),
% 0.99/1.19      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.99/1.19  thf('32', plain,
% 0.99/1.19      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.99/1.19        | ~ (v2_pre_topc @ sk_A)
% 0.99/1.19        | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.19      inference('sup-', [status(thm)], ['30', '31'])).
% 0.99/1.19  thf('33', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('35', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.99/1.19      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.99/1.19  thf('36', plain,
% 0.99/1.19      ((v3_tops_1 @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ sk_A)),
% 0.99/1.19      inference('demod', [status(thm)], ['27', '28', '29', '35'])).
% 0.99/1.19  thf('37', plain,
% 0.99/1.19      (((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.99/1.19         = (k2_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.99/1.19      inference('demod', [status(thm)], ['18', '24', '36'])).
% 0.99/1.19  thf('38', plain,
% 0.99/1.19      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.99/1.19         = (k1_xboole_0))),
% 0.99/1.19      inference('demod', [status(thm)], ['9', '37'])).
% 0.99/1.19  thf('39', plain,
% 0.99/1.19      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.19        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('demod', [status(thm)], ['2', '3'])).
% 0.99/1.19  thf(l78_tops_1, axiom,
% 0.99/1.19    (![A:$i]:
% 0.99/1.19     ( ( l1_pre_topc @ A ) =>
% 0.99/1.19       ( ![B:$i]:
% 0.99/1.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.19           ( ( k2_tops_1 @ A @ B ) =
% 0.99/1.19             ( k7_subset_1 @
% 0.99/1.19               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.99/1.19               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.99/1.19  thf('40', plain,
% 0.99/1.19      (![X20 : $i, X21 : $i]:
% 0.99/1.19         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.99/1.19          | ((k2_tops_1 @ X21 @ X20)
% 0.99/1.19              = (k7_subset_1 @ (u1_struct_0 @ X21) @ 
% 0.99/1.19                 (k2_pre_topc @ X21 @ X20) @ (k1_tops_1 @ X21 @ X20)))
% 0.99/1.19          | ~ (l1_pre_topc @ X21))),
% 0.99/1.19      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.99/1.19  thf('41', plain,
% 0.99/1.19      ((~ (l1_pre_topc @ sk_A)
% 0.99/1.19        | ((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.99/1.19            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.19               (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.99/1.19               (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.19      inference('sup-', [status(thm)], ['39', '40'])).
% 0.99/1.19  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('43', plain,
% 0.99/1.19      (((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.99/1.19         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.19            (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.99/1.19            (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.99/1.19      inference('demod', [status(thm)], ['41', '42'])).
% 0.99/1.19  thf('44', plain,
% 0.99/1.19      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.19        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('demod', [status(thm)], ['2', '3'])).
% 0.99/1.19  thf(dt_k2_pre_topc, axiom,
% 0.99/1.19    (![A:$i,B:$i]:
% 0.99/1.19     ( ( ( l1_pre_topc @ A ) & 
% 0.99/1.19         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.19       ( m1_subset_1 @
% 0.99/1.19         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.99/1.19  thf('45', plain,
% 0.99/1.19      (![X3 : $i, X4 : $i]:
% 0.99/1.19         (~ (l1_pre_topc @ X3)
% 0.99/1.19          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.99/1.19          | (m1_subset_1 @ (k2_pre_topc @ X3 @ X4) @ 
% 0.99/1.19             (k1_zfmisc_1 @ (u1_struct_0 @ X3))))),
% 0.99/1.19      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.99/1.19  thf('46', plain,
% 0.99/1.19      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.99/1.19         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.99/1.19        | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.19      inference('sup-', [status(thm)], ['44', '45'])).
% 0.99/1.19  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('48', plain,
% 0.99/1.19      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.99/1.19        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('demod', [status(thm)], ['46', '47'])).
% 0.99/1.19  thf('49', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf(t49_pre_topc, axiom,
% 0.99/1.19    (![A:$i]:
% 0.99/1.19     ( ( l1_pre_topc @ A ) =>
% 0.99/1.19       ( ![B:$i]:
% 0.99/1.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.19           ( ![C:$i]:
% 0.99/1.19             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.19               ( ( r1_tarski @ B @ C ) =>
% 0.99/1.19                 ( r1_tarski @
% 0.99/1.19                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 0.99/1.19  thf('50', plain,
% 0.99/1.19      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.99/1.19         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.99/1.19          | ~ (r1_tarski @ X7 @ X9)
% 0.99/1.19          | (r1_tarski @ (k2_pre_topc @ X8 @ X7) @ (k2_pre_topc @ X8 @ X9))
% 0.99/1.19          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.99/1.19          | ~ (l1_pre_topc @ X8))),
% 0.99/1.19      inference('cnf', [status(esa)], [t49_pre_topc])).
% 0.99/1.19  thf('51', plain,
% 0.99/1.19      (![X0 : $i]:
% 0.99/1.19         (~ (l1_pre_topc @ sk_A)
% 0.99/1.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.99/1.19          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.99/1.19             (k2_pre_topc @ sk_A @ X0))
% 0.99/1.19          | ~ (r1_tarski @ sk_B @ X0))),
% 0.99/1.19      inference('sup-', [status(thm)], ['49', '50'])).
% 0.99/1.19  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('53', plain,
% 0.99/1.19      (![X0 : $i]:
% 0.99/1.19         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.99/1.19          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.99/1.19             (k2_pre_topc @ sk_A @ X0))
% 0.99/1.19          | ~ (r1_tarski @ sk_B @ X0))),
% 0.99/1.19      inference('demod', [status(thm)], ['51', '52'])).
% 0.99/1.19  thf('54', plain,
% 0.99/1.19      ((~ (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.99/1.19        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.99/1.19           (k2_pre_topc @ sk_A @ 
% 0.99/1.19            (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))))),
% 0.99/1.19      inference('sup-', [status(thm)], ['48', '53'])).
% 0.99/1.19  thf('55', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf(d6_tops_1, axiom,
% 0.99/1.19    (![A:$i]:
% 0.99/1.19     ( ( l1_pre_topc @ A ) =>
% 0.99/1.19       ( ![B:$i]:
% 0.99/1.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.19           ( ( v4_tops_1 @ B @ A ) <=>
% 0.99/1.19             ( ( r1_tarski @ ( k1_tops_1 @ A @ ( k2_pre_topc @ A @ B ) ) @ B ) & 
% 0.99/1.19               ( r1_tarski @ B @ ( k2_pre_topc @ A @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.99/1.19  thf('56', plain,
% 0.99/1.19      (![X10 : $i, X11 : $i]:
% 0.99/1.19         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.99/1.19          | ~ (v4_tops_1 @ X10 @ X11)
% 0.99/1.19          | (r1_tarski @ X10 @ (k2_pre_topc @ X11 @ (k1_tops_1 @ X11 @ X10)))
% 0.99/1.19          | ~ (l1_pre_topc @ X11))),
% 0.99/1.19      inference('cnf', [status(esa)], [d6_tops_1])).
% 0.99/1.19  thf('57', plain,
% 0.99/1.19      ((~ (l1_pre_topc @ sk_A)
% 0.99/1.19        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.99/1.19        | ~ (v4_tops_1 @ sk_B @ sk_A))),
% 0.99/1.19      inference('sup-', [status(thm)], ['55', '56'])).
% 0.99/1.19  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('59', plain, ((v4_tops_1 @ sk_B @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('60', plain,
% 0.99/1.19      ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.19      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.99/1.19  thf('61', plain,
% 0.99/1.19      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.19        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('demod', [status(thm)], ['2', '3'])).
% 0.99/1.19  thf(projectivity_k2_pre_topc, axiom,
% 0.99/1.19    (![A:$i,B:$i]:
% 0.99/1.19     ( ( ( l1_pre_topc @ A ) & 
% 0.99/1.19         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.19       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.99/1.19         ( k2_pre_topc @ A @ B ) ) ))).
% 0.99/1.19  thf('62', plain,
% 0.99/1.19      (![X5 : $i, X6 : $i]:
% 0.99/1.19         (~ (l1_pre_topc @ X5)
% 0.99/1.19          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.99/1.19          | ((k2_pre_topc @ X5 @ (k2_pre_topc @ X5 @ X6))
% 0.99/1.19              = (k2_pre_topc @ X5 @ X6)))),
% 0.99/1.19      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 0.99/1.19  thf('63', plain,
% 0.99/1.19      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.99/1.19          = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.99/1.19        | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.19      inference('sup-', [status(thm)], ['61', '62'])).
% 0.99/1.19  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('65', plain,
% 0.99/1.19      (((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.99/1.19         = (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.19      inference('demod', [status(thm)], ['63', '64'])).
% 0.99/1.19  thf('66', plain,
% 0.99/1.19      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.99/1.19        (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.19      inference('demod', [status(thm)], ['54', '60', '65'])).
% 0.99/1.19  thf(d10_xboole_0, axiom,
% 0.99/1.19    (![A:$i,B:$i]:
% 0.99/1.19     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.99/1.19  thf('67', plain,
% 0.99/1.19      (![X0 : $i, X2 : $i]:
% 0.99/1.19         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.99/1.19      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.99/1.19  thf('68', plain,
% 0.99/1.19      ((~ (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.99/1.19           (k2_pre_topc @ sk_A @ sk_B))
% 0.99/1.19        | ((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.99/1.19            = (k2_pre_topc @ sk_A @ sk_B)))),
% 0.99/1.19      inference('sup-', [status(thm)], ['66', '67'])).
% 0.99/1.19  thf('69', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('70', plain,
% 0.99/1.19      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.99/1.19        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('demod', [status(thm)], ['2', '3'])).
% 0.99/1.19  thf('71', plain,
% 0.99/1.19      (![X12 : $i, X13 : $i]:
% 0.99/1.19         (~ (l1_pre_topc @ X12)
% 0.99/1.19          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.99/1.19          | (m1_subset_1 @ (k1_tops_1 @ X12 @ X13) @ 
% 0.99/1.19             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 0.99/1.19      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.99/1.19  thf('72', plain,
% 0.99/1.19      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.99/1.19         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.99/1.19        | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.19      inference('sup-', [status(thm)], ['70', '71'])).
% 0.99/1.19  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('74', plain,
% 0.99/1.19      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.99/1.19        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('demod', [status(thm)], ['72', '73'])).
% 0.99/1.19  thf('75', plain,
% 0.99/1.19      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.99/1.19         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.99/1.19          | ~ (r1_tarski @ X7 @ X9)
% 0.99/1.19          | (r1_tarski @ (k2_pre_topc @ X8 @ X7) @ (k2_pre_topc @ X8 @ X9))
% 0.99/1.19          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.99/1.19          | ~ (l1_pre_topc @ X8))),
% 0.99/1.19      inference('cnf', [status(esa)], [t49_pre_topc])).
% 0.99/1.19  thf('76', plain,
% 0.99/1.19      (![X0 : $i]:
% 0.99/1.19         (~ (l1_pre_topc @ sk_A)
% 0.99/1.19          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.99/1.19          | (r1_tarski @ 
% 0.99/1.19             (k2_pre_topc @ sk_A @ 
% 0.99/1.19              (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 0.99/1.19             (k2_pre_topc @ sk_A @ X0))
% 0.99/1.19          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ X0))),
% 0.99/1.19      inference('sup-', [status(thm)], ['74', '75'])).
% 0.99/1.19  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('78', plain,
% 0.99/1.19      (![X0 : $i]:
% 0.99/1.19         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.99/1.19          | (r1_tarski @ 
% 0.99/1.19             (k2_pre_topc @ sk_A @ 
% 0.99/1.19              (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))) @ 
% 0.99/1.19             (k2_pre_topc @ sk_A @ X0))
% 0.99/1.19          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ X0))),
% 0.99/1.19      inference('demod', [status(thm)], ['76', '77'])).
% 0.99/1.19  thf('79', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf(projectivity_k1_tops_1, axiom,
% 0.99/1.19    (![A:$i,B:$i]:
% 0.99/1.19     ( ( ( l1_pre_topc @ A ) & 
% 0.99/1.19         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.19       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 0.99/1.19  thf('80', plain,
% 0.99/1.19      (![X24 : $i, X25 : $i]:
% 0.99/1.19         (~ (l1_pre_topc @ X24)
% 0.99/1.19          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.99/1.19          | ((k1_tops_1 @ X24 @ (k1_tops_1 @ X24 @ X25))
% 0.99/1.19              = (k1_tops_1 @ X24 @ X25)))),
% 0.99/1.19      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 0.99/1.19  thf('81', plain,
% 0.99/1.19      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.99/1.19          = (k1_tops_1 @ sk_A @ sk_B))
% 0.99/1.19        | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.19      inference('sup-', [status(thm)], ['79', '80'])).
% 0.99/1.19  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('83', plain,
% 0.99/1.19      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.99/1.19         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.99/1.19      inference('demod', [status(thm)], ['81', '82'])).
% 0.99/1.19  thf('84', plain,
% 0.99/1.19      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.99/1.19         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.99/1.19      inference('demod', [status(thm)], ['81', '82'])).
% 0.99/1.19  thf('85', plain,
% 0.99/1.19      (![X0 : $i]:
% 0.99/1.19         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.99/1.19          | (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.99/1.19             (k2_pre_topc @ sk_A @ X0))
% 0.99/1.19          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 0.99/1.19      inference('demod', [status(thm)], ['78', '83', '84'])).
% 0.99/1.19  thf('86', plain,
% 0.99/1.19      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.99/1.19        | (r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.99/1.19           (k2_pre_topc @ sk_A @ sk_B)))),
% 0.99/1.19      inference('sup-', [status(thm)], ['69', '85'])).
% 0.99/1.19  thf('87', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf(t44_tops_1, axiom,
% 0.99/1.19    (![A:$i]:
% 0.99/1.19     ( ( l1_pre_topc @ A ) =>
% 0.99/1.19       ( ![B:$i]:
% 0.99/1.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.19           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.99/1.19  thf('88', plain,
% 0.99/1.19      (![X26 : $i, X27 : $i]:
% 0.99/1.19         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.99/1.19          | (r1_tarski @ (k1_tops_1 @ X27 @ X26) @ X26)
% 0.99/1.19          | ~ (l1_pre_topc @ X27))),
% 0.99/1.19      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.99/1.19  thf('89', plain,
% 0.99/1.19      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.99/1.19      inference('sup-', [status(thm)], ['87', '88'])).
% 0.99/1.19  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('91', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.99/1.19      inference('demod', [status(thm)], ['89', '90'])).
% 0.99/1.19  thf('92', plain,
% 0.99/1.19      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)) @ 
% 0.99/1.19        (k2_pre_topc @ sk_A @ sk_B))),
% 0.99/1.19      inference('demod', [status(thm)], ['86', '91'])).
% 0.99/1.19  thf('93', plain,
% 0.99/1.19      (((k2_pre_topc @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.99/1.19         = (k2_pre_topc @ sk_A @ sk_B))),
% 0.99/1.19      inference('demod', [status(thm)], ['68', '92'])).
% 0.99/1.19  thf('94', plain,
% 0.99/1.19      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.99/1.19         = (k1_tops_1 @ sk_A @ sk_B))),
% 0.99/1.19      inference('demod', [status(thm)], ['81', '82'])).
% 0.99/1.19  thf('95', plain,
% 0.99/1.19      (((k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B))
% 0.99/1.19         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.99/1.19            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.19      inference('demod', [status(thm)], ['43', '93', '94'])).
% 0.99/1.19  thf('96', plain,
% 0.99/1.19      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('97', plain,
% 0.99/1.19      (![X20 : $i, X21 : $i]:
% 0.99/1.19         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.99/1.19          | ((k2_tops_1 @ X21 @ X20)
% 0.99/1.19              = (k7_subset_1 @ (u1_struct_0 @ X21) @ 
% 0.99/1.19                 (k2_pre_topc @ X21 @ X20) @ (k1_tops_1 @ X21 @ X20)))
% 0.99/1.19          | ~ (l1_pre_topc @ X21))),
% 0.99/1.19      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.99/1.19  thf('98', plain,
% 0.99/1.19      ((~ (l1_pre_topc @ sk_A)
% 0.99/1.19        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.19            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.99/1.19               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.99/1.19      inference('sup-', [status(thm)], ['96', '97'])).
% 0.99/1.19  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('100', plain,
% 0.99/1.19      (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.19         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.99/1.19            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.19      inference('demod', [status(thm)], ['98', '99'])).
% 0.99/1.19  thf('101', plain,
% 0.99/1.19      (((k2_tops_1 @ sk_A @ sk_B)
% 0.99/1.19         = (k2_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_B)))),
% 0.99/1.19      inference('sup+', [status(thm)], ['95', '100'])).
% 0.99/1.19  thf('102', plain,
% 0.99/1.19      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.99/1.19      inference('demod', [status(thm)], ['38', '101'])).
% 0.99/1.19  thf('103', plain,
% 0.99/1.19      (((k1_tops_1 @ sk_A @ (k2_tops_1 @ sk_A @ sk_B)) != (k1_xboole_0))),
% 0.99/1.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.19  thf('104', plain, ($false),
% 0.99/1.19      inference('simplify_reflect-', [status(thm)], ['102', '103'])).
% 0.99/1.19  
% 0.99/1.19  % SZS output end Refutation
% 0.99/1.19  
% 1.03/1.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
