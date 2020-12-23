%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7k6pX3YlfQ

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:30 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 164 expanded)
%              Number of leaves         :   26 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  742 (1853 expanded)
%              Number of equality atoms :   13 (  25 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(t91_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_tops_1 @ B @ A )
             => ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t91_tops_1])).

thf('0',plain,(
    ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('4',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t41_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X5 @ ( k4_subset_1 @ X5 @ X6 @ X4 ) ) @ ( k3_subset_1 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t41_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k2_pre_topc @ X22 @ X21 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 @ ( k2_tops_1 @ X22 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('17',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k1_tops_1 @ X12 @ X11 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k2_pre_topc @ X12 @ ( k3_subset_1 @ ( u1_struct_0 @ X12 ) @ X11 ) ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X3 @ ( k3_subset_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('23',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','23'])).

thf('25',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['9','14','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('27',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('28',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('32',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','23'])).

thf('34',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t79_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v1_tops_1 @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( v1_tops_1 @ C @ A ) ) ) ) ) )).

thf('35',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v1_tops_1 @ X23 @ X24 )
      | ~ ( r1_tarski @ X23 @ X25 )
      | ( v1_tops_1 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t79_tops_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_tops_1 @ X0 @ sk_A )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ X0 )
      | ~ ( v1_tops_1 @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('39',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v2_tops_1 @ X13 @ X14 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X14 ) @ X13 ) @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('40',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','23'])).

thf('43',plain,
    ( ( v1_tops_1 @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
          <=> ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) )).

thf('45',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_tops_1 @ X15 @ X16 )
      | ( v2_tops_1 @ ( k2_pre_topc @ X16 @ X15 ) @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    v1_tops_1 @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['43','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_tops_1 @ X0 @ sk_A )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37','50'])).

thf('52',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','51'])).

thf('53',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('54',plain,(
    v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['0','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7k6pX3YlfQ
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:05:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.06/1.27  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.06/1.27  % Solved by: fo/fo7.sh
% 1.06/1.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.27  % done 831 iterations in 0.789s
% 1.06/1.27  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.06/1.27  % SZS output start Refutation
% 1.06/1.27  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.06/1.27  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.06/1.27  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.27  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.06/1.27  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 1.06/1.27  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.06/1.27  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 1.06/1.27  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.27  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.06/1.27  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 1.06/1.27  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.27  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.06/1.27  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.27  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.06/1.27  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.06/1.27  thf(t91_tops_1, conjecture,
% 1.06/1.27    (![A:$i]:
% 1.06/1.27     ( ( l1_pre_topc @ A ) =>
% 1.06/1.27       ( ![B:$i]:
% 1.06/1.27         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.27           ( ( v3_tops_1 @ B @ A ) =>
% 1.06/1.27             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 1.06/1.27  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.27    (~( ![A:$i]:
% 1.06/1.27        ( ( l1_pre_topc @ A ) =>
% 1.06/1.27          ( ![B:$i]:
% 1.06/1.27            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.27              ( ( v3_tops_1 @ B @ A ) =>
% 1.06/1.27                ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 1.06/1.27    inference('cnf.neg', [status(esa)], [t91_tops_1])).
% 1.06/1.27  thf('0', plain,
% 1.06/1.27      (~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('1', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('2', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf(dt_k2_tops_1, axiom,
% 1.06/1.27    (![A:$i,B:$i]:
% 1.06/1.27     ( ( ( l1_pre_topc @ A ) & 
% 1.06/1.27         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.06/1.27       ( m1_subset_1 @
% 1.06/1.27         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.06/1.27  thf('3', plain,
% 1.06/1.27      (![X17 : $i, X18 : $i]:
% 1.06/1.27         (~ (l1_pre_topc @ X17)
% 1.06/1.27          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.06/1.27          | (m1_subset_1 @ (k2_tops_1 @ X17 @ X18) @ 
% 1.06/1.27             (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 1.06/1.27      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 1.06/1.27  thf('4', plain,
% 1.06/1.27      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.06/1.27         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.06/1.27        | ~ (l1_pre_topc @ sk_A))),
% 1.06/1.27      inference('sup-', [status(thm)], ['2', '3'])).
% 1.06/1.27  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('6', plain,
% 1.06/1.27      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.06/1.27        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.27      inference('demod', [status(thm)], ['4', '5'])).
% 1.06/1.27  thf(t41_subset_1, axiom,
% 1.06/1.27    (![A:$i,B:$i]:
% 1.06/1.27     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.27       ( ![C:$i]:
% 1.06/1.27         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.27           ( r1_tarski @
% 1.06/1.27             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 1.06/1.27             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 1.06/1.27  thf('7', plain,
% 1.06/1.27      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.06/1.27         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 1.06/1.27          | (r1_tarski @ (k3_subset_1 @ X5 @ (k4_subset_1 @ X5 @ X6 @ X4)) @ 
% 1.06/1.27             (k3_subset_1 @ X5 @ X6))
% 1.06/1.27          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 1.06/1.27      inference('cnf', [status(esa)], [t41_subset_1])).
% 1.06/1.27  thf('8', plain,
% 1.06/1.27      (![X0 : $i]:
% 1.06/1.27         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.06/1.27          | (r1_tarski @ 
% 1.06/1.27             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.27              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 1.06/1.27               (k2_tops_1 @ sk_A @ sk_B))) @ 
% 1.06/1.27             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['6', '7'])).
% 1.06/1.27  thf('9', plain,
% 1.06/1.27      ((r1_tarski @ 
% 1.06/1.27        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.27         (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))) @ 
% 1.06/1.27        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.06/1.27      inference('sup-', [status(thm)], ['1', '8'])).
% 1.06/1.27  thf('10', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf(t65_tops_1, axiom,
% 1.06/1.27    (![A:$i]:
% 1.06/1.27     ( ( l1_pre_topc @ A ) =>
% 1.06/1.27       ( ![B:$i]:
% 1.06/1.27         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.27           ( ( k2_pre_topc @ A @ B ) =
% 1.06/1.27             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.06/1.27  thf('11', plain,
% 1.06/1.27      (![X21 : $i, X22 : $i]:
% 1.06/1.27         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.06/1.27          | ((k2_pre_topc @ X22 @ X21)
% 1.06/1.27              = (k4_subset_1 @ (u1_struct_0 @ X22) @ X21 @ 
% 1.06/1.27                 (k2_tops_1 @ X22 @ X21)))
% 1.06/1.27          | ~ (l1_pre_topc @ X22))),
% 1.06/1.27      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.06/1.27  thf('12', plain,
% 1.06/1.27      ((~ (l1_pre_topc @ sk_A)
% 1.06/1.27        | ((k2_pre_topc @ sk_A @ sk_B)
% 1.06/1.27            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['10', '11'])).
% 1.06/1.27  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('14', plain,
% 1.06/1.27      (((k2_pre_topc @ sk_A @ sk_B)
% 1.06/1.27         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.06/1.27            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.06/1.27      inference('demod', [status(thm)], ['12', '13'])).
% 1.06/1.27  thf('15', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf(dt_k3_subset_1, axiom,
% 1.06/1.27    (![A:$i,B:$i]:
% 1.06/1.27     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.27       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.06/1.27  thf('16', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]:
% 1.06/1.27         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 1.06/1.27          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.06/1.27      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.06/1.27  thf('17', plain,
% 1.06/1.27      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.06/1.27        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['15', '16'])).
% 1.06/1.27  thf(d1_tops_1, axiom,
% 1.06/1.27    (![A:$i]:
% 1.06/1.27     ( ( l1_pre_topc @ A ) =>
% 1.06/1.27       ( ![B:$i]:
% 1.06/1.27         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.27           ( ( k1_tops_1 @ A @ B ) =
% 1.06/1.27             ( k3_subset_1 @
% 1.06/1.27               ( u1_struct_0 @ A ) @ 
% 1.06/1.27               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 1.06/1.27  thf('18', plain,
% 1.06/1.27      (![X11 : $i, X12 : $i]:
% 1.06/1.27         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 1.06/1.27          | ((k1_tops_1 @ X12 @ X11)
% 1.06/1.27              = (k3_subset_1 @ (u1_struct_0 @ X12) @ 
% 1.06/1.27                 (k2_pre_topc @ X12 @ (k3_subset_1 @ (u1_struct_0 @ X12) @ X11))))
% 1.06/1.27          | ~ (l1_pre_topc @ X12))),
% 1.06/1.27      inference('cnf', [status(esa)], [d1_tops_1])).
% 1.06/1.27  thf('19', plain,
% 1.06/1.27      ((~ (l1_pre_topc @ sk_A)
% 1.06/1.27        | ((k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.06/1.27            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.27               (k2_pre_topc @ sk_A @ 
% 1.06/1.27                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.27                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['17', '18'])).
% 1.06/1.27  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('21', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf(involutiveness_k3_subset_1, axiom,
% 1.06/1.27    (![A:$i,B:$i]:
% 1.06/1.27     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.27       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.06/1.27  thf('22', plain,
% 1.06/1.27      (![X2 : $i, X3 : $i]:
% 1.06/1.27         (((k3_subset_1 @ X3 @ (k3_subset_1 @ X3 @ X2)) = (X2))
% 1.06/1.27          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 1.06/1.27      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.06/1.27  thf('23', plain,
% 1.06/1.27      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.27         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.06/1.27      inference('sup-', [status(thm)], ['21', '22'])).
% 1.06/1.27  thf('24', plain,
% 1.06/1.27      (((k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.06/1.27         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 1.06/1.27      inference('demod', [status(thm)], ['19', '20', '23'])).
% 1.06/1.27  thf('25', plain,
% 1.06/1.27      ((r1_tarski @ 
% 1.06/1.27        (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.06/1.27        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.06/1.27      inference('demod', [status(thm)], ['9', '14', '24'])).
% 1.06/1.27  thf('26', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf(dt_k2_pre_topc, axiom,
% 1.06/1.27    (![A:$i,B:$i]:
% 1.06/1.27     ( ( ( l1_pre_topc @ A ) & 
% 1.06/1.27         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.06/1.27       ( m1_subset_1 @
% 1.06/1.27         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.06/1.27  thf('27', plain,
% 1.06/1.27      (![X7 : $i, X8 : $i]:
% 1.06/1.27         (~ (l1_pre_topc @ X7)
% 1.06/1.27          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 1.06/1.27          | (m1_subset_1 @ (k2_pre_topc @ X7 @ X8) @ 
% 1.06/1.27             (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 1.06/1.27      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.06/1.27  thf('28', plain,
% 1.06/1.27      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.06/1.27         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.06/1.27        | ~ (l1_pre_topc @ sk_A))),
% 1.06/1.27      inference('sup-', [status(thm)], ['26', '27'])).
% 1.06/1.27  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('30', plain,
% 1.06/1.27      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.06/1.27        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.27      inference('demod', [status(thm)], ['28', '29'])).
% 1.06/1.27  thf('31', plain,
% 1.06/1.27      (![X0 : $i, X1 : $i]:
% 1.06/1.27         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 1.06/1.27          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.06/1.27      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.06/1.27  thf('32', plain,
% 1.06/1.27      ((m1_subset_1 @ 
% 1.06/1.27        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 1.06/1.27        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['30', '31'])).
% 1.06/1.27  thf('33', plain,
% 1.06/1.27      (((k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.06/1.27         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 1.06/1.27      inference('demod', [status(thm)], ['19', '20', '23'])).
% 1.06/1.27  thf('34', plain,
% 1.06/1.27      ((m1_subset_1 @ 
% 1.06/1.27        (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.06/1.27        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.27      inference('demod', [status(thm)], ['32', '33'])).
% 1.06/1.27  thf(t79_tops_1, axiom,
% 1.06/1.27    (![A:$i]:
% 1.06/1.27     ( ( l1_pre_topc @ A ) =>
% 1.06/1.27       ( ![B:$i]:
% 1.06/1.27         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.27           ( ![C:$i]:
% 1.06/1.27             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.27               ( ( ( v1_tops_1 @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 1.06/1.27                 ( v1_tops_1 @ C @ A ) ) ) ) ) ) ))).
% 1.06/1.27  thf('35', plain,
% 1.06/1.27      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.06/1.27         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.06/1.27          | ~ (v1_tops_1 @ X23 @ X24)
% 1.06/1.27          | ~ (r1_tarski @ X23 @ X25)
% 1.06/1.27          | (v1_tops_1 @ X25 @ X24)
% 1.06/1.27          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.06/1.27          | ~ (l1_pre_topc @ X24))),
% 1.06/1.27      inference('cnf', [status(esa)], [t79_tops_1])).
% 1.06/1.27  thf('36', plain,
% 1.06/1.27      (![X0 : $i]:
% 1.06/1.27         (~ (l1_pre_topc @ sk_A)
% 1.06/1.27          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.06/1.27          | (v1_tops_1 @ X0 @ sk_A)
% 1.06/1.27          | ~ (r1_tarski @ 
% 1.06/1.27               (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.06/1.27               X0)
% 1.06/1.27          | ~ (v1_tops_1 @ 
% 1.06/1.27               (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.06/1.27               sk_A))),
% 1.06/1.27      inference('sup-', [status(thm)], ['34', '35'])).
% 1.06/1.27  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('38', plain,
% 1.06/1.27      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 1.06/1.27        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.27      inference('demod', [status(thm)], ['28', '29'])).
% 1.06/1.27  thf(d4_tops_1, axiom,
% 1.06/1.27    (![A:$i]:
% 1.06/1.27     ( ( l1_pre_topc @ A ) =>
% 1.06/1.27       ( ![B:$i]:
% 1.06/1.27         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.27           ( ( v2_tops_1 @ B @ A ) <=>
% 1.06/1.27             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 1.06/1.27  thf('39', plain,
% 1.06/1.27      (![X13 : $i, X14 : $i]:
% 1.06/1.27         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.06/1.27          | ~ (v2_tops_1 @ X13 @ X14)
% 1.06/1.27          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X14) @ X13) @ X14)
% 1.06/1.27          | ~ (l1_pre_topc @ X14))),
% 1.06/1.27      inference('cnf', [status(esa)], [d4_tops_1])).
% 1.06/1.27  thf('40', plain,
% 1.06/1.27      ((~ (l1_pre_topc @ sk_A)
% 1.06/1.27        | (v1_tops_1 @ 
% 1.06/1.27           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 1.06/1.27           sk_A)
% 1.06/1.27        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 1.06/1.27      inference('sup-', [status(thm)], ['38', '39'])).
% 1.06/1.27  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('42', plain,
% 1.06/1.27      (((k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.06/1.27         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 1.06/1.27      inference('demod', [status(thm)], ['19', '20', '23'])).
% 1.06/1.27  thf('43', plain,
% 1.06/1.27      (((v1_tops_1 @ 
% 1.06/1.27         (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.06/1.27         sk_A)
% 1.06/1.27        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 1.06/1.27      inference('demod', [status(thm)], ['40', '41', '42'])).
% 1.06/1.27  thf('44', plain,
% 1.06/1.27      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf(d5_tops_1, axiom,
% 1.06/1.27    (![A:$i]:
% 1.06/1.27     ( ( l1_pre_topc @ A ) =>
% 1.06/1.27       ( ![B:$i]:
% 1.06/1.27         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.27           ( ( v3_tops_1 @ B @ A ) <=>
% 1.06/1.27             ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ))).
% 1.06/1.27  thf('45', plain,
% 1.06/1.27      (![X15 : $i, X16 : $i]:
% 1.06/1.27         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 1.06/1.27          | ~ (v3_tops_1 @ X15 @ X16)
% 1.06/1.27          | (v2_tops_1 @ (k2_pre_topc @ X16 @ X15) @ X16)
% 1.06/1.27          | ~ (l1_pre_topc @ X16))),
% 1.06/1.27      inference('cnf', [status(esa)], [d5_tops_1])).
% 1.06/1.27  thf('46', plain,
% 1.06/1.27      ((~ (l1_pre_topc @ sk_A)
% 1.06/1.27        | (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 1.06/1.27        | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 1.06/1.27      inference('sup-', [status(thm)], ['44', '45'])).
% 1.06/1.27  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('48', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 1.06/1.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.27  thf('49', plain, ((v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 1.06/1.27      inference('demod', [status(thm)], ['46', '47', '48'])).
% 1.06/1.27  thf('50', plain,
% 1.06/1.27      ((v1_tops_1 @ 
% 1.06/1.27        (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ sk_A)),
% 1.06/1.27      inference('demod', [status(thm)], ['43', '49'])).
% 1.06/1.27  thf('51', plain,
% 1.06/1.27      (![X0 : $i]:
% 1.06/1.27         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.06/1.27          | (v1_tops_1 @ X0 @ sk_A)
% 1.06/1.27          | ~ (r1_tarski @ 
% 1.06/1.27               (k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.06/1.27               X0))),
% 1.06/1.27      inference('demod', [status(thm)], ['36', '37', '50'])).
% 1.06/1.27  thf('52', plain,
% 1.06/1.27      (((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.06/1.27        | ~ (m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.06/1.27             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.06/1.27      inference('sup-', [status(thm)], ['25', '51'])).
% 1.06/1.27  thf('53', plain,
% 1.06/1.27      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.06/1.27        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.06/1.27      inference('sup-', [status(thm)], ['15', '16'])).
% 1.06/1.27  thf('54', plain,
% 1.06/1.27      ((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 1.06/1.27      inference('demod', [status(thm)], ['52', '53'])).
% 1.06/1.27  thf('55', plain, ($false), inference('demod', [status(thm)], ['0', '54'])).
% 1.06/1.27  
% 1.06/1.27  % SZS output end Refutation
% 1.06/1.27  
% 1.06/1.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
