%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.As84F8Bn3L

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:35 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 630 expanded)
%              Number of leaves         :   29 ( 191 expanded)
%              Depth                    :   17
%              Number of atoms          : 1586 (8868 expanded)
%              Number of equality atoms :   95 ( 429 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t76_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k1_tops_1 @ X34 @ X33 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X34 ) @ X33 @ ( k2_tops_1 @ X34 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k7_subset_1 @ X13 @ X12 @ X14 )
        = ( k4_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( k2_tops_1 @ X28 @ X27 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X28 ) @ ( k2_pre_topc @ X28 @ X27 ) @ ( k1_tops_1 @ X28 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k7_subset_1 @ X13 @ X12 @ X14 )
        = ( k4_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11','18'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k7_subset_1 @ X16 @ X17 @ X15 )
        = ( k9_subset_1 @ X16 @ X17 @ ( k3_subset_1 @ X16 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k7_subset_1 @ X0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) )
        = ( k9_subset_1 @ X0 @ X2 @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k7_subset_1 @ X0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) )
        = ( k9_subset_1 @ X0 @ X2 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X2 ) )
      = ( k9_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('32',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( ( k7_subset_1 @ X13 @ X12 @ X14 )
        = ( k4_xboole_0 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ X2 ) )
      = ( k9_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(idempotence_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ B )
        = B ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k9_subset_1 @ X8 @ X7 @ X7 )
        = X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[idempotence_k9_subset_1])).

thf('37',plain,(
    ! [X0: $i,X2: $i] :
      ( ( k9_subset_1 @ X0 @ X2 @ X2 )
      = X2 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['19','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('41',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['40','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('45',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( r1_tarski @ X23 @ ( k2_pre_topc @ X24 @ X23 ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('51',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('52',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('55',plain,
    ( ( k3_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('57',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['52','55','56'])).

thf('58',plain,
    ( ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['43','57'])).

thf('59',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['59'])).

thf('61',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['41'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( v3_pre_topc @ D @ B )
                     => ( ( k1_tops_1 @ B @ D )
                        = D ) )
                    & ( ( ( k1_tops_1 @ A @ C )
                        = C )
                     => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf('63',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_pre_topc @ X30 @ X29 )
      | ( ( k1_tops_1 @ X29 @ X30 )
        = X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('64',plain,
    ( ! [X29: $i,X30: $i] :
        ( ~ ( l1_pre_topc @ X29 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
        | ~ ( v3_pre_topc @ X30 @ X29 )
        | ( ( k1_tops_1 @ X29 @ X30 )
          = X30 ) )
   <= ! [X29: $i,X30: $i] :
        ( ~ ( l1_pre_topc @ X29 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
        | ~ ( v3_pre_topc @ X30 @ X29 )
        | ( ( k1_tops_1 @ X29 @ X30 )
          = X30 ) ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ! [X31: $i,X32: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( l1_pre_topc @ X32 )
        | ~ ( v2_pre_topc @ X32 ) )
   <= ! [X31: $i,X32: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( l1_pre_topc @ X32 )
        | ~ ( v2_pre_topc @ X32 ) ) ),
    inference(split,[status(esa)],['63'])).

thf('67',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X31: $i,X32: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( l1_pre_topc @ X32 )
        | ~ ( v2_pre_topc @ X32 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ~ ! [X31: $i,X32: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( l1_pre_topc @ X32 )
        | ~ ( v2_pre_topc @ X32 ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ! [X29: $i,X30: $i] :
        ( ~ ( l1_pre_topc @ X29 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
        | ~ ( v3_pre_topc @ X30 @ X29 )
        | ( ( k1_tops_1 @ X29 @ X30 )
          = X30 ) )
    | ! [X31: $i,X32: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( l1_pre_topc @ X32 )
        | ~ ( v2_pre_topc @ X32 ) ) ),
    inference(split,[status(esa)],['63'])).

thf('72',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_pre_topc @ X30 @ X29 )
      | ( ( k1_tops_1 @ X29 @ X30 )
        = X30 ) ) ),
    inference('sat_resolution*',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_pre_topc @ X30 @ X29 )
      | ( ( k1_tops_1 @ X29 @ X30 )
        = X30 ) ) ),
    inference(simpl_trail,[status(thm)],['64','72'])).

thf('74',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['62','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['61','76'])).

thf('78',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11','18'])).

thf('79',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('81',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['59'])).

thf('82',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( ( ( k2_tops_1 @ sk_A @ sk_B )
       != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
      & ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['41'])).

thf('86',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['60','84','85'])).

thf('87',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['58','86'])).

thf('88',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11','18'])).

thf('89',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','11','18'])).

thf('90',plain,
    ( ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['58','86'])).

thf('91',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['39','87','88','89','90'])).

thf('92',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['7','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('95',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('98',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('100',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['95','98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('102',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( ( k1_tops_1 @ X32 @ X31 )
       != X31 )
      | ( v3_pre_topc @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('103',plain,
    ( ! [X31: $i,X32: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( l1_pre_topc @ X32 )
        | ~ ( v2_pre_topc @ X32 )
        | ( ( k1_tops_1 @ X32 @ X31 )
         != X31 )
        | ( v3_pre_topc @ X31 @ X32 ) )
   <= ! [X31: $i,X32: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( l1_pre_topc @ X32 )
        | ~ ( v2_pre_topc @ X32 )
        | ( ( k1_tops_1 @ X32 @ X31 )
         != X31 )
        | ( v3_pre_topc @ X31 @ X32 ) ) ),
    inference(split,[status(esa)],['102'])).

thf('104',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ! [X29: $i,X30: $i] :
        ( ~ ( l1_pre_topc @ X29 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) )
   <= ! [X29: $i,X30: $i] :
        ( ~ ( l1_pre_topc @ X29 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference(split,[status(esa)],['102'])).

thf('106',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X29: $i,X30: $i] :
        ( ~ ( l1_pre_topc @ X29 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ~ ! [X29: $i,X30: $i] :
        ( ~ ( l1_pre_topc @ X29 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ! [X31: $i,X32: $i] :
        ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
        | ~ ( l1_pre_topc @ X32 )
        | ~ ( v2_pre_topc @ X32 )
        | ( ( k1_tops_1 @ X32 @ X31 )
         != X31 )
        | ( v3_pre_topc @ X31 @ X32 ) )
    | ! [X29: $i,X30: $i] :
        ( ~ ( l1_pre_topc @ X29 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) ) ) ),
    inference(split,[status(esa)],['102'])).

thf('110',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( ( k1_tops_1 @ X32 @ X31 )
       != X31 )
      | ( v3_pre_topc @ X31 @ X32 ) ) ),
    inference('sat_resolution*',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( ( k1_tops_1 @ X32 @ X31 )
       != X31 )
      | ( v3_pre_topc @ X31 @ X32 ) ) ),
    inference(simpl_trail,[status(thm)],['103','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
       != ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','111'])).

thf('113',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['100','112'])).

thf('114',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['95','98','99'])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['95','98','99'])).

thf('118',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != sk_B )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['113','114','115','116','117'])).

thf('119',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['59'])).

thf('120',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['60','84'])).

thf('121',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['119','120'])).

thf('122',plain,(
    ( k1_tops_1 @ sk_A @ sk_B )
 != sk_B ),
    inference(clc,[status(thm)],['118','121'])).

thf('123',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['92','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.As84F8Bn3L
% 0.13/0.36  % Computer   : n022.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 19:39:11 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.80/1.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.80/1.03  % Solved by: fo/fo7.sh
% 0.80/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.80/1.03  % done 863 iterations in 0.557s
% 0.80/1.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.80/1.03  % SZS output start Refutation
% 0.80/1.03  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.80/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.80/1.03  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.80/1.03  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.80/1.03  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.80/1.03  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.80/1.03  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.80/1.03  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.80/1.03  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.80/1.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.80/1.03  thf(sk_B_type, type, sk_B: $i).
% 0.80/1.03  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.80/1.03  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.80/1.03  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.80/1.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.80/1.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.80/1.03  thf(t76_tops_1, conjecture,
% 0.80/1.03    (![A:$i]:
% 0.80/1.03     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.80/1.03       ( ![B:$i]:
% 0.80/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.03           ( ( v3_pre_topc @ B @ A ) <=>
% 0.80/1.03             ( ( k2_tops_1 @ A @ B ) =
% 0.80/1.03               ( k7_subset_1 @
% 0.80/1.03                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 0.80/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.80/1.03    (~( ![A:$i]:
% 0.80/1.03        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.80/1.03          ( ![B:$i]:
% 0.80/1.03            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.03              ( ( v3_pre_topc @ B @ A ) <=>
% 0.80/1.03                ( ( k2_tops_1 @ A @ B ) =
% 0.80/1.03                  ( k7_subset_1 @
% 0.80/1.03                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 0.80/1.03    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 0.80/1.03  thf('0', plain,
% 0.80/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf(t74_tops_1, axiom,
% 0.80/1.03    (![A:$i]:
% 0.80/1.03     ( ( l1_pre_topc @ A ) =>
% 0.80/1.03       ( ![B:$i]:
% 0.80/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.03           ( ( k1_tops_1 @ A @ B ) =
% 0.80/1.03             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.80/1.03  thf('1', plain,
% 0.80/1.03      (![X33 : $i, X34 : $i]:
% 0.80/1.03         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.80/1.03          | ((k1_tops_1 @ X34 @ X33)
% 0.80/1.03              = (k7_subset_1 @ (u1_struct_0 @ X34) @ X33 @ 
% 0.80/1.03                 (k2_tops_1 @ X34 @ X33)))
% 0.80/1.03          | ~ (l1_pre_topc @ X34))),
% 0.80/1.03      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.80/1.03  thf('2', plain,
% 0.80/1.03      ((~ (l1_pre_topc @ sk_A)
% 0.80/1.03        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.80/1.03            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.80/1.03               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.80/1.03      inference('sup-', [status(thm)], ['0', '1'])).
% 0.80/1.03  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('4', plain,
% 0.80/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf(redefinition_k7_subset_1, axiom,
% 0.80/1.03    (![A:$i,B:$i,C:$i]:
% 0.80/1.03     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.80/1.03       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.80/1.03  thf('5', plain,
% 0.80/1.03      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.80/1.03         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.80/1.03          | ((k7_subset_1 @ X13 @ X12 @ X14) = (k4_xboole_0 @ X12 @ X14)))),
% 0.80/1.03      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.80/1.03  thf('6', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.80/1.03           = (k4_xboole_0 @ sk_B @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['4', '5'])).
% 0.80/1.03  thf('7', plain,
% 0.80/1.03      (((k1_tops_1 @ sk_A @ sk_B)
% 0.80/1.03         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.80/1.03      inference('demod', [status(thm)], ['2', '3', '6'])).
% 0.80/1.03  thf('8', plain,
% 0.80/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf(l78_tops_1, axiom,
% 0.80/1.03    (![A:$i]:
% 0.80/1.03     ( ( l1_pre_topc @ A ) =>
% 0.80/1.03       ( ![B:$i]:
% 0.80/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.03           ( ( k2_tops_1 @ A @ B ) =
% 0.80/1.03             ( k7_subset_1 @
% 0.80/1.03               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.80/1.03               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.80/1.03  thf('9', plain,
% 0.80/1.03      (![X27 : $i, X28 : $i]:
% 0.80/1.03         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.80/1.03          | ((k2_tops_1 @ X28 @ X27)
% 0.80/1.03              = (k7_subset_1 @ (u1_struct_0 @ X28) @ 
% 0.80/1.03                 (k2_pre_topc @ X28 @ X27) @ (k1_tops_1 @ X28 @ X27)))
% 0.80/1.03          | ~ (l1_pre_topc @ X28))),
% 0.80/1.03      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.80/1.03  thf('10', plain,
% 0.80/1.03      ((~ (l1_pre_topc @ sk_A)
% 0.80/1.03        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.80/1.03            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.03               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.80/1.03      inference('sup-', [status(thm)], ['8', '9'])).
% 0.80/1.03  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('12', plain,
% 0.80/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf(dt_k2_pre_topc, axiom,
% 0.80/1.03    (![A:$i,B:$i]:
% 0.80/1.03     ( ( ( l1_pre_topc @ A ) & 
% 0.80/1.03         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.80/1.03       ( m1_subset_1 @
% 0.80/1.03         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.80/1.03  thf('13', plain,
% 0.80/1.03      (![X21 : $i, X22 : $i]:
% 0.80/1.03         (~ (l1_pre_topc @ X21)
% 0.80/1.03          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.80/1.03          | (m1_subset_1 @ (k2_pre_topc @ X21 @ X22) @ 
% 0.80/1.03             (k1_zfmisc_1 @ (u1_struct_0 @ X21))))),
% 0.80/1.03      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.80/1.03  thf('14', plain,
% 0.80/1.03      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.80/1.03         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.80/1.03        | ~ (l1_pre_topc @ sk_A))),
% 0.80/1.03      inference('sup-', [status(thm)], ['12', '13'])).
% 0.80/1.03  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('16', plain,
% 0.80/1.03      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.80/1.03        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.03      inference('demod', [status(thm)], ['14', '15'])).
% 0.80/1.03  thf('17', plain,
% 0.80/1.03      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.80/1.03         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.80/1.03          | ((k7_subset_1 @ X13 @ X12 @ X14) = (k4_xboole_0 @ X12 @ X14)))),
% 0.80/1.03      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.80/1.03  thf('18', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.80/1.03           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['16', '17'])).
% 0.80/1.03  thf('19', plain,
% 0.80/1.03      (((k2_tops_1 @ sk_A @ sk_B)
% 0.80/1.03         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.80/1.03            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.80/1.03      inference('demod', [status(thm)], ['10', '11', '18'])).
% 0.80/1.03  thf(t36_xboole_1, axiom,
% 0.80/1.03    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.80/1.03  thf('20', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.80/1.03      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.80/1.03  thf(t3_subset, axiom,
% 0.80/1.03    (![A:$i,B:$i]:
% 0.80/1.03     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.80/1.03  thf('21', plain,
% 0.80/1.03      (![X18 : $i, X20 : $i]:
% 0.80/1.03         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 0.80/1.03      inference('cnf', [status(esa)], [t3_subset])).
% 0.80/1.03  thf('22', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['20', '21'])).
% 0.80/1.03  thf('23', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['20', '21'])).
% 0.80/1.03  thf(t32_subset_1, axiom,
% 0.80/1.03    (![A:$i,B:$i]:
% 0.80/1.03     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.80/1.03       ( ![C:$i]:
% 0.80/1.03         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.80/1.03           ( ( k7_subset_1 @ A @ B @ C ) =
% 0.80/1.03             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.80/1.03  thf('24', plain,
% 0.80/1.03      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.80/1.03         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.80/1.03          | ((k7_subset_1 @ X16 @ X17 @ X15)
% 0.80/1.03              = (k9_subset_1 @ X16 @ X17 @ (k3_subset_1 @ X16 @ X15)))
% 0.80/1.03          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.80/1.03      inference('cnf', [status(esa)], [t32_subset_1])).
% 0.80/1.03  thf('25', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.03         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 0.80/1.03          | ((k7_subset_1 @ X0 @ X2 @ (k4_xboole_0 @ X0 @ X1))
% 0.80/1.03              = (k9_subset_1 @ X0 @ X2 @ 
% 0.80/1.03                 (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1)))))),
% 0.80/1.03      inference('sup-', [status(thm)], ['23', '24'])).
% 0.80/1.03  thf('26', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['20', '21'])).
% 0.80/1.03  thf(d5_subset_1, axiom,
% 0.80/1.03    (![A:$i,B:$i]:
% 0.80/1.03     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.80/1.03       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.80/1.03  thf('27', plain,
% 0.80/1.03      (![X2 : $i, X3 : $i]:
% 0.80/1.03         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.80/1.03          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.80/1.03      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.80/1.03  thf('28', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.80/1.03           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['26', '27'])).
% 0.80/1.03  thf('29', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.03         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 0.80/1.03          | ((k7_subset_1 @ X0 @ X2 @ (k4_xboole_0 @ X0 @ X1))
% 0.80/1.03              = (k9_subset_1 @ X0 @ X2 @ 
% 0.80/1.03                 (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))))),
% 0.80/1.03      inference('demod', [status(thm)], ['25', '28'])).
% 0.80/1.03  thf('30', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.03         ((k7_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X2))
% 0.80/1.03           = (k9_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 0.80/1.03              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X2))))),
% 0.80/1.03      inference('sup-', [status(thm)], ['22', '29'])).
% 0.80/1.03  thf('31', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['20', '21'])).
% 0.80/1.03  thf('32', plain,
% 0.80/1.03      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.80/1.03         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.80/1.03          | ((k7_subset_1 @ X13 @ X12 @ X14) = (k4_xboole_0 @ X12 @ X14)))),
% 0.80/1.03      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.80/1.03  thf('33', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.03         ((k7_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 0.80/1.03           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 0.80/1.03      inference('sup-', [status(thm)], ['31', '32'])).
% 0.80/1.03  thf('34', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.03         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X0 @ X2))
% 0.80/1.03           = (k9_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1) @ 
% 0.80/1.03              (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X2))))),
% 0.80/1.03      inference('demod', [status(thm)], ['30', '33'])).
% 0.80/1.03  thf('35', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['20', '21'])).
% 0.80/1.03  thf(idempotence_k9_subset_1, axiom,
% 0.80/1.03    (![A:$i,B:$i,C:$i]:
% 0.80/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.80/1.03       ( ( k9_subset_1 @ A @ B @ B ) = ( B ) ) ))).
% 0.80/1.03  thf('36', plain,
% 0.80/1.03      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.80/1.03         (((k9_subset_1 @ X8 @ X7 @ X7) = (X7))
% 0.80/1.03          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.80/1.03      inference('cnf', [status(esa)], [idempotence_k9_subset_1])).
% 0.80/1.03  thf('37', plain,
% 0.80/1.03      (![X0 : $i, X2 : $i]: ((k9_subset_1 @ X0 @ X2 @ X2) = (X2))),
% 0.80/1.03      inference('sup-', [status(thm)], ['35', '36'])).
% 0.80/1.03  thf('38', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 0.80/1.03           (k4_xboole_0 @ X1 @ X0))
% 0.80/1.03           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.80/1.03      inference('sup+', [status(thm)], ['34', '37'])).
% 0.80/1.03  thf('39', plain,
% 0.80/1.03      (((k4_xboole_0 @ 
% 0.80/1.03         (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B)) @ 
% 0.80/1.03         (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.80/1.03         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.80/1.03            (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.80/1.03             (k1_tops_1 @ sk_A @ sk_B))))),
% 0.80/1.03      inference('sup+', [status(thm)], ['19', '38'])).
% 0.80/1.03  thf('40', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.80/1.03           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['16', '17'])).
% 0.80/1.03  thf('41', plain,
% 0.80/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.80/1.03          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.03             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.80/1.03        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('42', plain,
% 0.80/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.80/1.03          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.03             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.80/1.03         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.80/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.03                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.80/1.03      inference('split', [status(esa)], ['41'])).
% 0.80/1.03  thf('43', plain,
% 0.80/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.80/1.03          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.80/1.03         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.80/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.03                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.80/1.03      inference('sup+', [status(thm)], ['40', '42'])).
% 0.80/1.03  thf('44', plain,
% 0.80/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf(t48_pre_topc, axiom,
% 0.80/1.03    (![A:$i]:
% 0.80/1.03     ( ( l1_pre_topc @ A ) =>
% 0.80/1.03       ( ![B:$i]:
% 0.80/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.03           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.80/1.03  thf('45', plain,
% 0.80/1.03      (![X23 : $i, X24 : $i]:
% 0.80/1.03         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.80/1.03          | (r1_tarski @ X23 @ (k2_pre_topc @ X24 @ X23))
% 0.80/1.03          | ~ (l1_pre_topc @ X24))),
% 0.80/1.03      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.80/1.03  thf('46', plain,
% 0.80/1.03      ((~ (l1_pre_topc @ sk_A)
% 0.80/1.03        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['44', '45'])).
% 0.80/1.03  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('48', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.80/1.03      inference('demod', [status(thm)], ['46', '47'])).
% 0.80/1.03  thf('49', plain,
% 0.80/1.03      (![X18 : $i, X20 : $i]:
% 0.80/1.03         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 0.80/1.03      inference('cnf', [status(esa)], [t3_subset])).
% 0.80/1.03  thf('50', plain,
% 0.80/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['48', '49'])).
% 0.80/1.03  thf(involutiveness_k3_subset_1, axiom,
% 0.80/1.03    (![A:$i,B:$i]:
% 0.80/1.03     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.80/1.03       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.80/1.03  thf('51', plain,
% 0.80/1.03      (![X10 : $i, X11 : $i]:
% 0.80/1.03         (((k3_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X10)) = (X10))
% 0.80/1.03          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.80/1.03      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.80/1.03  thf('52', plain,
% 0.80/1.03      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.80/1.03         (k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)) = (sk_B))),
% 0.80/1.03      inference('sup-', [status(thm)], ['50', '51'])).
% 0.80/1.03  thf('53', plain,
% 0.80/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['48', '49'])).
% 0.80/1.03  thf('54', plain,
% 0.80/1.03      (![X2 : $i, X3 : $i]:
% 0.80/1.03         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.80/1.03          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.80/1.03      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.80/1.03  thf('55', plain,
% 0.80/1.03      (((k3_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 0.80/1.03         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 0.80/1.03      inference('sup-', [status(thm)], ['53', '54'])).
% 0.80/1.03  thf('56', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.80/1.03           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['26', '27'])).
% 0.80/1.03  thf('57', plain,
% 0.80/1.03      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.80/1.03         (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)) = (sk_B))),
% 0.80/1.03      inference('demod', [status(thm)], ['52', '55', '56'])).
% 0.80/1.03  thf('58', plain,
% 0.80/1.03      ((((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.80/1.03          = (sk_B)))
% 0.80/1.03         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.80/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.03                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.80/1.03      inference('sup+', [status(thm)], ['43', '57'])).
% 0.80/1.03  thf('59', plain,
% 0.80/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.80/1.03          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.03              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.80/1.03        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('60', plain,
% 0.80/1.03      (~ ((v3_pre_topc @ sk_B @ sk_A)) | 
% 0.80/1.03       ~
% 0.80/1.03       (((k2_tops_1 @ sk_A @ sk_B)
% 0.80/1.03          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.03             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.80/1.03      inference('split', [status(esa)], ['59'])).
% 0.80/1.03  thf('61', plain,
% 0.80/1.03      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.80/1.03      inference('split', [status(esa)], ['41'])).
% 0.80/1.03  thf('62', plain,
% 0.80/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf(t55_tops_1, axiom,
% 0.80/1.03    (![A:$i]:
% 0.80/1.03     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.80/1.03       ( ![B:$i]:
% 0.80/1.03         ( ( l1_pre_topc @ B ) =>
% 0.80/1.03           ( ![C:$i]:
% 0.80/1.03             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.80/1.03               ( ![D:$i]:
% 0.80/1.03                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.80/1.03                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.80/1.03                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.80/1.03                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.80/1.03                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.80/1.03  thf('63', plain,
% 0.80/1.03      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.80/1.03         (~ (l1_pre_topc @ X29)
% 0.80/1.03          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.80/1.03          | ~ (v3_pre_topc @ X30 @ X29)
% 0.80/1.03          | ((k1_tops_1 @ X29 @ X30) = (X30))
% 0.80/1.03          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.80/1.03          | ~ (l1_pre_topc @ X32)
% 0.80/1.03          | ~ (v2_pre_topc @ X32))),
% 0.80/1.03      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.80/1.03  thf('64', plain,
% 0.80/1.03      ((![X29 : $i, X30 : $i]:
% 0.80/1.03          (~ (l1_pre_topc @ X29)
% 0.80/1.03           | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.80/1.03           | ~ (v3_pre_topc @ X30 @ X29)
% 0.80/1.03           | ((k1_tops_1 @ X29 @ X30) = (X30))))
% 0.80/1.03         <= ((![X29 : $i, X30 : $i]:
% 0.80/1.03                (~ (l1_pre_topc @ X29)
% 0.80/1.03                 | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.80/1.03                 | ~ (v3_pre_topc @ X30 @ X29)
% 0.80/1.03                 | ((k1_tops_1 @ X29 @ X30) = (X30)))))),
% 0.80/1.03      inference('split', [status(esa)], ['63'])).
% 0.80/1.03  thf('65', plain,
% 0.80/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('66', plain,
% 0.80/1.03      ((![X31 : $i, X32 : $i]:
% 0.80/1.03          (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.80/1.03           | ~ (l1_pre_topc @ X32)
% 0.80/1.03           | ~ (v2_pre_topc @ X32)))
% 0.80/1.03         <= ((![X31 : $i, X32 : $i]:
% 0.80/1.03                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.80/1.03                 | ~ (l1_pre_topc @ X32)
% 0.80/1.03                 | ~ (v2_pre_topc @ X32))))),
% 0.80/1.03      inference('split', [status(esa)], ['63'])).
% 0.80/1.03  thf('67', plain,
% 0.80/1.03      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.80/1.03         <= ((![X31 : $i, X32 : $i]:
% 0.80/1.03                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.80/1.03                 | ~ (l1_pre_topc @ X32)
% 0.80/1.03                 | ~ (v2_pre_topc @ X32))))),
% 0.80/1.03      inference('sup-', [status(thm)], ['65', '66'])).
% 0.80/1.03  thf('68', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('70', plain,
% 0.80/1.03      (~
% 0.80/1.03       (![X31 : $i, X32 : $i]:
% 0.80/1.03          (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.80/1.03           | ~ (l1_pre_topc @ X32)
% 0.80/1.03           | ~ (v2_pre_topc @ X32)))),
% 0.80/1.03      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.80/1.03  thf('71', plain,
% 0.80/1.03      ((![X29 : $i, X30 : $i]:
% 0.80/1.03          (~ (l1_pre_topc @ X29)
% 0.80/1.03           | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.80/1.03           | ~ (v3_pre_topc @ X30 @ X29)
% 0.80/1.03           | ((k1_tops_1 @ X29 @ X30) = (X30)))) | 
% 0.80/1.03       (![X31 : $i, X32 : $i]:
% 0.80/1.03          (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.80/1.03           | ~ (l1_pre_topc @ X32)
% 0.80/1.03           | ~ (v2_pre_topc @ X32)))),
% 0.80/1.03      inference('split', [status(esa)], ['63'])).
% 0.80/1.03  thf('72', plain,
% 0.80/1.03      ((![X29 : $i, X30 : $i]:
% 0.80/1.03          (~ (l1_pre_topc @ X29)
% 0.80/1.03           | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.80/1.03           | ~ (v3_pre_topc @ X30 @ X29)
% 0.80/1.03           | ((k1_tops_1 @ X29 @ X30) = (X30))))),
% 0.80/1.03      inference('sat_resolution*', [status(thm)], ['70', '71'])).
% 0.80/1.03  thf('73', plain,
% 0.80/1.03      (![X29 : $i, X30 : $i]:
% 0.80/1.03         (~ (l1_pre_topc @ X29)
% 0.80/1.03          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.80/1.03          | ~ (v3_pre_topc @ X30 @ X29)
% 0.80/1.03          | ((k1_tops_1 @ X29 @ X30) = (X30)))),
% 0.80/1.03      inference('simpl_trail', [status(thm)], ['64', '72'])).
% 0.80/1.03  thf('74', plain,
% 0.80/1.03      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B))
% 0.80/1.03        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.80/1.03        | ~ (l1_pre_topc @ sk_A))),
% 0.80/1.03      inference('sup-', [status(thm)], ['62', '73'])).
% 0.80/1.03  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('76', plain,
% 0.80/1.03      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)) | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.80/1.03      inference('demod', [status(thm)], ['74', '75'])).
% 0.80/1.03  thf('77', plain,
% 0.80/1.03      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 0.80/1.03         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['61', '76'])).
% 0.80/1.03  thf('78', plain,
% 0.80/1.03      (((k2_tops_1 @ sk_A @ sk_B)
% 0.80/1.03         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.80/1.03            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.80/1.03      inference('demod', [status(thm)], ['10', '11', '18'])).
% 0.80/1.03  thf('79', plain,
% 0.80/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.80/1.03          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.80/1.03         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.80/1.03      inference('sup+', [status(thm)], ['77', '78'])).
% 0.80/1.03  thf('80', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.80/1.03           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['16', '17'])).
% 0.80/1.03  thf('81', plain,
% 0.80/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.80/1.03          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.03              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.80/1.03         <= (~
% 0.80/1.03             (((k2_tops_1 @ sk_A @ sk_B)
% 0.80/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.03                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.80/1.03      inference('split', [status(esa)], ['59'])).
% 0.80/1.03  thf('82', plain,
% 0.80/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.80/1.03          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.80/1.03         <= (~
% 0.80/1.03             (((k2_tops_1 @ sk_A @ sk_B)
% 0.80/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.03                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.80/1.03      inference('sup-', [status(thm)], ['80', '81'])).
% 0.80/1.03  thf('83', plain,
% 0.80/1.03      ((((k2_tops_1 @ sk_A @ sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 0.80/1.03         <= (~
% 0.80/1.03             (((k2_tops_1 @ sk_A @ sk_B)
% 0.80/1.03                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.03                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) & 
% 0.80/1.03             ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['79', '82'])).
% 0.80/1.03  thf('84', plain,
% 0.80/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.80/1.03          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.03             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.80/1.03       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.80/1.03      inference('simplify', [status(thm)], ['83'])).
% 0.80/1.03  thf('85', plain,
% 0.80/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.80/1.03          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.03             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.80/1.03       ((v3_pre_topc @ sk_B @ sk_A))),
% 0.80/1.03      inference('split', [status(esa)], ['41'])).
% 0.80/1.03  thf('86', plain,
% 0.80/1.03      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.80/1.03          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.03             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.80/1.03      inference('sat_resolution*', [status(thm)], ['60', '84', '85'])).
% 0.80/1.03  thf('87', plain,
% 0.80/1.03      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.80/1.03         = (sk_B))),
% 0.80/1.03      inference('simpl_trail', [status(thm)], ['58', '86'])).
% 0.80/1.03  thf('88', plain,
% 0.80/1.03      (((k2_tops_1 @ sk_A @ sk_B)
% 0.80/1.03         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.80/1.03            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.80/1.03      inference('demod', [status(thm)], ['10', '11', '18'])).
% 0.80/1.03  thf('89', plain,
% 0.80/1.03      (((k2_tops_1 @ sk_A @ sk_B)
% 0.80/1.03         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.80/1.03            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.80/1.03      inference('demod', [status(thm)], ['10', '11', '18'])).
% 0.80/1.03  thf('90', plain,
% 0.80/1.03      (((k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_tops_1 @ sk_A @ sk_B))
% 0.80/1.03         = (sk_B))),
% 0.80/1.03      inference('simpl_trail', [status(thm)], ['58', '86'])).
% 0.80/1.03  thf('91', plain,
% 0.80/1.03      (((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B))),
% 0.80/1.03      inference('demod', [status(thm)], ['39', '87', '88', '89', '90'])).
% 0.80/1.03  thf('92', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.80/1.03      inference('sup+', [status(thm)], ['7', '91'])).
% 0.80/1.03  thf('93', plain,
% 0.80/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('94', plain,
% 0.80/1.03      (![X10 : $i, X11 : $i]:
% 0.80/1.03         (((k3_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X10)) = (X10))
% 0.80/1.03          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.80/1.03      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.80/1.03  thf('95', plain,
% 0.80/1.03      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.03         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.80/1.03      inference('sup-', [status(thm)], ['93', '94'])).
% 0.80/1.03  thf('96', plain,
% 0.80/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('97', plain,
% 0.80/1.03      (![X2 : $i, X3 : $i]:
% 0.80/1.03         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.80/1.03          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.80/1.03      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.80/1.03  thf('98', plain,
% 0.80/1.03      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.80/1.03         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.80/1.03      inference('sup-', [status(thm)], ['96', '97'])).
% 0.80/1.03  thf('99', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.80/1.03           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['26', '27'])).
% 0.80/1.03  thf('100', plain,
% 0.80/1.03      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.03         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.80/1.03      inference('demod', [status(thm)], ['95', '98', '99'])).
% 0.80/1.03  thf('101', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['20', '21'])).
% 0.80/1.03  thf('102', plain,
% 0.80/1.03      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.80/1.03         (~ (l1_pre_topc @ X29)
% 0.80/1.03          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.80/1.03          | ((k1_tops_1 @ X32 @ X31) != (X31))
% 0.80/1.03          | (v3_pre_topc @ X31 @ X32)
% 0.80/1.03          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.80/1.03          | ~ (l1_pre_topc @ X32)
% 0.80/1.03          | ~ (v2_pre_topc @ X32))),
% 0.80/1.03      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.80/1.03  thf('103', plain,
% 0.80/1.03      ((![X31 : $i, X32 : $i]:
% 0.80/1.03          (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.80/1.03           | ~ (l1_pre_topc @ X32)
% 0.80/1.03           | ~ (v2_pre_topc @ X32)
% 0.80/1.03           | ((k1_tops_1 @ X32 @ X31) != (X31))
% 0.80/1.03           | (v3_pre_topc @ X31 @ X32)))
% 0.80/1.03         <= ((![X31 : $i, X32 : $i]:
% 0.80/1.03                (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.80/1.03                 | ~ (l1_pre_topc @ X32)
% 0.80/1.03                 | ~ (v2_pre_topc @ X32)
% 0.80/1.03                 | ((k1_tops_1 @ X32 @ X31) != (X31))
% 0.80/1.03                 | (v3_pre_topc @ X31 @ X32))))),
% 0.80/1.03      inference('split', [status(esa)], ['102'])).
% 0.80/1.03  thf('104', plain,
% 0.80/1.03      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('105', plain,
% 0.80/1.03      ((![X29 : $i, X30 : $i]:
% 0.80/1.03          (~ (l1_pre_topc @ X29)
% 0.80/1.03           | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))))
% 0.80/1.03         <= ((![X29 : $i, X30 : $i]:
% 0.80/1.03                (~ (l1_pre_topc @ X29)
% 0.80/1.03                 | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29))))))),
% 0.80/1.03      inference('split', [status(esa)], ['102'])).
% 0.80/1.03  thf('106', plain,
% 0.80/1.03      ((~ (l1_pre_topc @ sk_A))
% 0.80/1.03         <= ((![X29 : $i, X30 : $i]:
% 0.80/1.03                (~ (l1_pre_topc @ X29)
% 0.80/1.03                 | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29))))))),
% 0.80/1.03      inference('sup-', [status(thm)], ['104', '105'])).
% 0.80/1.03  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('108', plain,
% 0.80/1.03      (~
% 0.80/1.03       (![X29 : $i, X30 : $i]:
% 0.80/1.03          (~ (l1_pre_topc @ X29)
% 0.80/1.03           | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))))),
% 0.80/1.03      inference('demod', [status(thm)], ['106', '107'])).
% 0.80/1.03  thf('109', plain,
% 0.80/1.03      ((![X31 : $i, X32 : $i]:
% 0.80/1.03          (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.80/1.03           | ~ (l1_pre_topc @ X32)
% 0.80/1.03           | ~ (v2_pre_topc @ X32)
% 0.80/1.03           | ((k1_tops_1 @ X32 @ X31) != (X31))
% 0.80/1.03           | (v3_pre_topc @ X31 @ X32))) | 
% 0.80/1.03       (![X29 : $i, X30 : $i]:
% 0.80/1.03          (~ (l1_pre_topc @ X29)
% 0.80/1.03           | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))))),
% 0.80/1.03      inference('split', [status(esa)], ['102'])).
% 0.80/1.03  thf('110', plain,
% 0.80/1.03      ((![X31 : $i, X32 : $i]:
% 0.80/1.03          (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.80/1.03           | ~ (l1_pre_topc @ X32)
% 0.80/1.03           | ~ (v2_pre_topc @ X32)
% 0.80/1.03           | ((k1_tops_1 @ X32 @ X31) != (X31))
% 0.80/1.03           | (v3_pre_topc @ X31 @ X32)))),
% 0.80/1.03      inference('sat_resolution*', [status(thm)], ['108', '109'])).
% 0.80/1.03  thf('111', plain,
% 0.80/1.03      (![X31 : $i, X32 : $i]:
% 0.80/1.03         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.80/1.03          | ~ (l1_pre_topc @ X32)
% 0.80/1.03          | ~ (v2_pre_topc @ X32)
% 0.80/1.03          | ((k1_tops_1 @ X32 @ X31) != (X31))
% 0.80/1.03          | (v3_pre_topc @ X31 @ X32))),
% 0.80/1.03      inference('simpl_trail', [status(thm)], ['103', '110'])).
% 0.80/1.03  thf('112', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         ((v3_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 0.80/1.03          | ((k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.80/1.03              != (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.80/1.03          | ~ (v2_pre_topc @ X0)
% 0.80/1.03          | ~ (l1_pre_topc @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['101', '111'])).
% 0.80/1.03  thf('113', plain,
% 0.80/1.03      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.80/1.03          != (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.03              (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.80/1.03        | ~ (l1_pre_topc @ sk_A)
% 0.80/1.03        | ~ (v2_pre_topc @ sk_A)
% 0.80/1.03        | (v3_pre_topc @ 
% 0.80/1.03           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.03            (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.80/1.03           sk_A))),
% 0.80/1.03      inference('sup-', [status(thm)], ['100', '112'])).
% 0.80/1.03  thf('114', plain,
% 0.80/1.03      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.03         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.80/1.03      inference('demod', [status(thm)], ['95', '98', '99'])).
% 0.80/1.03  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('116', plain, ((v2_pre_topc @ sk_A)),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('117', plain,
% 0.80/1.03      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.80/1.03         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.80/1.03      inference('demod', [status(thm)], ['95', '98', '99'])).
% 0.80/1.03  thf('118', plain,
% 0.80/1.03      ((((k1_tops_1 @ sk_A @ sk_B) != (sk_B)) | (v3_pre_topc @ sk_B @ sk_A))),
% 0.80/1.03      inference('demod', [status(thm)], ['113', '114', '115', '116', '117'])).
% 0.80/1.03  thf('119', plain,
% 0.80/1.03      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.80/1.03      inference('split', [status(esa)], ['59'])).
% 0.80/1.03  thf('120', plain, (~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.80/1.03      inference('sat_resolution*', [status(thm)], ['60', '84'])).
% 0.80/1.03  thf('121', plain, (~ (v3_pre_topc @ sk_B @ sk_A)),
% 0.80/1.03      inference('simpl_trail', [status(thm)], ['119', '120'])).
% 0.80/1.03  thf('122', plain, (((k1_tops_1 @ sk_A @ sk_B) != (sk_B))),
% 0.80/1.03      inference('clc', [status(thm)], ['118', '121'])).
% 0.80/1.03  thf('123', plain, ($false),
% 0.80/1.03      inference('simplify_reflect-', [status(thm)], ['92', '122'])).
% 0.80/1.03  
% 0.80/1.03  % SZS output end Refutation
% 0.80/1.03  
% 0.80/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
