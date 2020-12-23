%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RdYI34bCTP

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:03 EST 2020

% Result     : Theorem 18.95s
% Output     : Refutation 18.95s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 127 expanded)
%              Number of leaves         :   25 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  674 (1518 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t50_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k1_tops_1 @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( r1_tarski @ ( k1_tops_1 @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('9',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X27 @ X26 ) @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['10','11'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( ( k7_subset_1 @ X21 @ X20 @ X22 )
        = ( k4_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('24',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X23: $i,X25: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X23 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( r1_tarski @ X28 @ X30 )
      | ( r1_tarski @ ( k1_tops_1 @ X29 @ X28 ) @ ( k1_tops_1 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','32'])).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('37',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X27 @ X26 ) @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('41',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X3 @ X5 )
      | ~ ( r1_tarski @ X3 @ ( k4_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X27 @ X26 ) @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('48',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('49',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('50',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_C )
      | ( r1_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['42','51'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('53',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X17 @ X19 )
      | ( r1_tarski @ X17 @ ( k4_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['20','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RdYI34bCTP
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 18.95/19.16  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 18.95/19.16  % Solved by: fo/fo7.sh
% 18.95/19.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 18.95/19.16  % done 18529 iterations in 18.702s
% 18.95/19.16  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 18.95/19.16  % SZS output start Refutation
% 18.95/19.16  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 18.95/19.16  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 18.95/19.16  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 18.95/19.16  thf(sk_B_type, type, sk_B: $i).
% 18.95/19.16  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 18.95/19.16  thf(sk_A_type, type, sk_A: $i).
% 18.95/19.16  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 18.95/19.16  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 18.95/19.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 18.95/19.16  thf(sk_C_type, type, sk_C: $i).
% 18.95/19.16  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 18.95/19.16  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 18.95/19.16  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 18.95/19.16  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 18.95/19.16  thf(t50_tops_1, conjecture,
% 18.95/19.16    (![A:$i]:
% 18.95/19.16     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 18.95/19.16       ( ![B:$i]:
% 18.95/19.16         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 18.95/19.16           ( ![C:$i]:
% 18.95/19.16             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 18.95/19.16               ( r1_tarski @
% 18.95/19.16                 ( k1_tops_1 @
% 18.95/19.16                   A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 18.95/19.16                 ( k7_subset_1 @
% 18.95/19.16                   ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 18.95/19.16                   ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 18.95/19.16  thf(zf_stmt_0, negated_conjecture,
% 18.95/19.16    (~( ![A:$i]:
% 18.95/19.16        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 18.95/19.16          ( ![B:$i]:
% 18.95/19.16            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 18.95/19.16              ( ![C:$i]:
% 18.95/19.16                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 18.95/19.16                  ( r1_tarski @
% 18.95/19.16                    ( k1_tops_1 @
% 18.95/19.16                      A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 18.95/19.16                    ( k7_subset_1 @
% 18.95/19.16                      ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 18.95/19.16                      ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 18.95/19.16    inference('cnf.neg', [status(esa)], [t50_tops_1])).
% 18.95/19.16  thf('0', plain,
% 18.95/19.16      (~ (r1_tarski @ 
% 18.95/19.16          (k1_tops_1 @ sk_A @ 
% 18.95/19.16           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 18.95/19.16          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 18.95/19.16           (k1_tops_1 @ sk_A @ sk_C)))),
% 18.95/19.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.95/19.16  thf('1', plain,
% 18.95/19.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 18.95/19.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.95/19.16  thf(redefinition_k7_subset_1, axiom,
% 18.95/19.16    (![A:$i,B:$i,C:$i]:
% 18.95/19.16     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 18.95/19.16       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 18.95/19.16  thf('2', plain,
% 18.95/19.16      (![X20 : $i, X21 : $i, X22 : $i]:
% 18.95/19.16         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 18.95/19.16          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 18.95/19.16      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 18.95/19.16  thf('3', plain,
% 18.95/19.16      (![X0 : $i]:
% 18.95/19.16         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 18.95/19.16           = (k4_xboole_0 @ sk_B @ X0))),
% 18.95/19.16      inference('sup-', [status(thm)], ['1', '2'])).
% 18.95/19.16  thf('4', plain,
% 18.95/19.16      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 18.95/19.16          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 18.95/19.16           (k1_tops_1 @ sk_A @ sk_C)))),
% 18.95/19.16      inference('demod', [status(thm)], ['0', '3'])).
% 18.95/19.16  thf('5', plain,
% 18.95/19.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 18.95/19.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.95/19.16  thf(t3_subset, axiom,
% 18.95/19.16    (![A:$i,B:$i]:
% 18.95/19.16     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 18.95/19.16  thf('6', plain,
% 18.95/19.16      (![X23 : $i, X24 : $i]:
% 18.95/19.16         ((r1_tarski @ X23 @ X24) | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 18.95/19.16      inference('cnf', [status(esa)], [t3_subset])).
% 18.95/19.16  thf('7', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 18.95/19.16      inference('sup-', [status(thm)], ['5', '6'])).
% 18.95/19.16  thf('8', plain,
% 18.95/19.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 18.95/19.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.95/19.16  thf(t44_tops_1, axiom,
% 18.95/19.16    (![A:$i]:
% 18.95/19.16     ( ( l1_pre_topc @ A ) =>
% 18.95/19.16       ( ![B:$i]:
% 18.95/19.16         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 18.95/19.16           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 18.95/19.16  thf('9', plain,
% 18.95/19.16      (![X26 : $i, X27 : $i]:
% 18.95/19.16         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 18.95/19.16          | (r1_tarski @ (k1_tops_1 @ X27 @ X26) @ X26)
% 18.95/19.16          | ~ (l1_pre_topc @ X27))),
% 18.95/19.16      inference('cnf', [status(esa)], [t44_tops_1])).
% 18.95/19.16  thf('10', plain,
% 18.95/19.16      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 18.95/19.16      inference('sup-', [status(thm)], ['8', '9'])).
% 18.95/19.16  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 18.95/19.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.95/19.16  thf('12', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 18.95/19.16      inference('demod', [status(thm)], ['10', '11'])).
% 18.95/19.16  thf(t1_xboole_1, axiom,
% 18.95/19.16    (![A:$i,B:$i,C:$i]:
% 18.95/19.16     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 18.95/19.16       ( r1_tarski @ A @ C ) ))).
% 18.95/19.16  thf('13', plain,
% 18.95/19.16      (![X8 : $i, X9 : $i, X10 : $i]:
% 18.95/19.16         (~ (r1_tarski @ X8 @ X9)
% 18.95/19.16          | ~ (r1_tarski @ X9 @ X10)
% 18.95/19.16          | (r1_tarski @ X8 @ X10))),
% 18.95/19.16      inference('cnf', [status(esa)], [t1_xboole_1])).
% 18.95/19.16  thf('14', plain,
% 18.95/19.16      (![X0 : $i]:
% 18.95/19.16         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 18.95/19.16          | ~ (r1_tarski @ sk_B @ X0))),
% 18.95/19.16      inference('sup-', [status(thm)], ['12', '13'])).
% 18.95/19.16  thf('15', plain,
% 18.95/19.16      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 18.95/19.16      inference('sup-', [status(thm)], ['7', '14'])).
% 18.95/19.16  thf('16', plain,
% 18.95/19.16      (![X23 : $i, X25 : $i]:
% 18.95/19.16         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 18.95/19.16      inference('cnf', [status(esa)], [t3_subset])).
% 18.95/19.16  thf('17', plain,
% 18.95/19.16      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 18.95/19.16        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 18.95/19.16      inference('sup-', [status(thm)], ['15', '16'])).
% 18.95/19.16  thf('18', plain,
% 18.95/19.16      (![X20 : $i, X21 : $i, X22 : $i]:
% 18.95/19.16         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 18.95/19.16          | ((k7_subset_1 @ X21 @ X20 @ X22) = (k4_xboole_0 @ X20 @ X22)))),
% 18.95/19.16      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 18.95/19.16  thf('19', plain,
% 18.95/19.16      (![X0 : $i]:
% 18.95/19.16         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 18.95/19.16           = (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 18.95/19.16      inference('sup-', [status(thm)], ['17', '18'])).
% 18.95/19.16  thf('20', plain,
% 18.95/19.16      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 18.95/19.16          (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 18.95/19.16      inference('demod', [status(thm)], ['4', '19'])).
% 18.95/19.16  thf('21', plain,
% 18.95/19.16      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 18.95/19.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.95/19.16  thf('22', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 18.95/19.16      inference('sup-', [status(thm)], ['5', '6'])).
% 18.95/19.16  thf(t36_xboole_1, axiom,
% 18.95/19.16    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 18.95/19.16  thf('23', plain,
% 18.95/19.16      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 18.95/19.16      inference('cnf', [status(esa)], [t36_xboole_1])).
% 18.95/19.16  thf('24', plain,
% 18.95/19.16      (![X8 : $i, X9 : $i, X10 : $i]:
% 18.95/19.16         (~ (r1_tarski @ X8 @ X9)
% 18.95/19.16          | ~ (r1_tarski @ X9 @ X10)
% 18.95/19.16          | (r1_tarski @ X8 @ X10))),
% 18.95/19.16      inference('cnf', [status(esa)], [t1_xboole_1])).
% 18.95/19.16  thf('25', plain,
% 18.95/19.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 18.95/19.16         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 18.95/19.16      inference('sup-', [status(thm)], ['23', '24'])).
% 18.95/19.16  thf('26', plain,
% 18.95/19.16      (![X0 : $i]:
% 18.95/19.16         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 18.95/19.16      inference('sup-', [status(thm)], ['22', '25'])).
% 18.95/19.16  thf('27', plain,
% 18.95/19.16      (![X23 : $i, X25 : $i]:
% 18.95/19.16         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X23 @ X25))),
% 18.95/19.16      inference('cnf', [status(esa)], [t3_subset])).
% 18.95/19.16  thf('28', plain,
% 18.95/19.16      (![X0 : $i]:
% 18.95/19.16         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 18.95/19.16          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 18.95/19.16      inference('sup-', [status(thm)], ['26', '27'])).
% 18.95/19.16  thf(t48_tops_1, axiom,
% 18.95/19.16    (![A:$i]:
% 18.95/19.16     ( ( l1_pre_topc @ A ) =>
% 18.95/19.16       ( ![B:$i]:
% 18.95/19.16         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 18.95/19.16           ( ![C:$i]:
% 18.95/19.16             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 18.95/19.16               ( ( r1_tarski @ B @ C ) =>
% 18.95/19.16                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 18.95/19.16  thf('29', plain,
% 18.95/19.16      (![X28 : $i, X29 : $i, X30 : $i]:
% 18.95/19.16         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 18.95/19.16          | ~ (r1_tarski @ X28 @ X30)
% 18.95/19.16          | (r1_tarski @ (k1_tops_1 @ X29 @ X28) @ (k1_tops_1 @ X29 @ X30))
% 18.95/19.16          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 18.95/19.16          | ~ (l1_pre_topc @ X29))),
% 18.95/19.16      inference('cnf', [status(esa)], [t48_tops_1])).
% 18.95/19.16  thf('30', plain,
% 18.95/19.16      (![X0 : $i, X1 : $i]:
% 18.95/19.16         (~ (l1_pre_topc @ sk_A)
% 18.95/19.16          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 18.95/19.16          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 18.95/19.16             (k1_tops_1 @ sk_A @ X1))
% 18.95/19.16          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 18.95/19.16      inference('sup-', [status(thm)], ['28', '29'])).
% 18.95/19.16  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 18.95/19.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.95/19.16  thf('32', plain,
% 18.95/19.16      (![X0 : $i, X1 : $i]:
% 18.95/19.16         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 18.95/19.16          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 18.95/19.16             (k1_tops_1 @ sk_A @ X1))
% 18.95/19.16          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 18.95/19.16      inference('demod', [status(thm)], ['30', '31'])).
% 18.95/19.16  thf('33', plain,
% 18.95/19.16      (![X0 : $i]:
% 18.95/19.16         (~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_B)
% 18.95/19.16          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 18.95/19.16             (k1_tops_1 @ sk_A @ sk_B)))),
% 18.95/19.16      inference('sup-', [status(thm)], ['21', '32'])).
% 18.95/19.16  thf('34', plain,
% 18.95/19.16      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 18.95/19.16      inference('cnf', [status(esa)], [t36_xboole_1])).
% 18.95/19.16  thf('35', plain,
% 18.95/19.16      (![X0 : $i]:
% 18.95/19.16         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 18.95/19.16          (k1_tops_1 @ sk_A @ sk_B))),
% 18.95/19.16      inference('demod', [status(thm)], ['33', '34'])).
% 18.95/19.16  thf('36', plain,
% 18.95/19.16      (![X0 : $i]:
% 18.95/19.16         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 18.95/19.16          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 18.95/19.16      inference('sup-', [status(thm)], ['26', '27'])).
% 18.95/19.16  thf('37', plain,
% 18.95/19.16      (![X26 : $i, X27 : $i]:
% 18.95/19.16         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 18.95/19.16          | (r1_tarski @ (k1_tops_1 @ X27 @ X26) @ X26)
% 18.95/19.16          | ~ (l1_pre_topc @ X27))),
% 18.95/19.16      inference('cnf', [status(esa)], [t44_tops_1])).
% 18.95/19.16  thf('38', plain,
% 18.95/19.16      (![X0 : $i]:
% 18.95/19.16         (~ (l1_pre_topc @ sk_A)
% 18.95/19.16          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 18.95/19.16             (k4_xboole_0 @ sk_B @ X0)))),
% 18.95/19.16      inference('sup-', [status(thm)], ['36', '37'])).
% 18.95/19.16  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 18.95/19.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.95/19.16  thf('40', plain,
% 18.95/19.16      (![X0 : $i]:
% 18.95/19.16         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 18.95/19.16          (k4_xboole_0 @ sk_B @ X0))),
% 18.95/19.16      inference('demod', [status(thm)], ['38', '39'])).
% 18.95/19.16  thf(t106_xboole_1, axiom,
% 18.95/19.16    (![A:$i,B:$i,C:$i]:
% 18.95/19.16     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 18.95/19.16       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 18.95/19.16  thf('41', plain,
% 18.95/19.16      (![X3 : $i, X4 : $i, X5 : $i]:
% 18.95/19.16         ((r1_xboole_0 @ X3 @ X5)
% 18.95/19.16          | ~ (r1_tarski @ X3 @ (k4_xboole_0 @ X4 @ X5)))),
% 18.95/19.16      inference('cnf', [status(esa)], [t106_xboole_1])).
% 18.95/19.16  thf('42', plain,
% 18.95/19.16      (![X0 : $i]:
% 18.95/19.16         (r1_xboole_0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ X0)),
% 18.95/19.16      inference('sup-', [status(thm)], ['40', '41'])).
% 18.95/19.16  thf('43', plain,
% 18.95/19.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 18.95/19.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.95/19.16  thf('44', plain,
% 18.95/19.16      (![X26 : $i, X27 : $i]:
% 18.95/19.16         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 18.95/19.16          | (r1_tarski @ (k1_tops_1 @ X27 @ X26) @ X26)
% 18.95/19.16          | ~ (l1_pre_topc @ X27))),
% 18.95/19.16      inference('cnf', [status(esa)], [t44_tops_1])).
% 18.95/19.16  thf('45', plain,
% 18.95/19.16      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 18.95/19.16      inference('sup-', [status(thm)], ['43', '44'])).
% 18.95/19.16  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 18.95/19.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 18.95/19.16  thf('47', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 18.95/19.16      inference('demod', [status(thm)], ['45', '46'])).
% 18.95/19.16  thf(t12_xboole_1, axiom,
% 18.95/19.16    (![A:$i,B:$i]:
% 18.95/19.16     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 18.95/19.16  thf('48', plain,
% 18.95/19.16      (![X6 : $i, X7 : $i]:
% 18.95/19.16         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 18.95/19.16      inference('cnf', [status(esa)], [t12_xboole_1])).
% 18.95/19.16  thf('49', plain,
% 18.95/19.16      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C) = (sk_C))),
% 18.95/19.16      inference('sup-', [status(thm)], ['47', '48'])).
% 18.95/19.16  thf(t70_xboole_1, axiom,
% 18.95/19.16    (![A:$i,B:$i,C:$i]:
% 18.95/19.16     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 18.95/19.16            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 18.95/19.16       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 18.95/19.16            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 18.95/19.16  thf('50', plain,
% 18.95/19.16      (![X13 : $i, X14 : $i, X16 : $i]:
% 18.95/19.16         ((r1_xboole_0 @ X13 @ X14)
% 18.95/19.16          | ~ (r1_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X16)))),
% 18.95/19.16      inference('cnf', [status(esa)], [t70_xboole_1])).
% 18.95/19.16  thf('51', plain,
% 18.95/19.16      (![X0 : $i]:
% 18.95/19.16         (~ (r1_xboole_0 @ X0 @ sk_C)
% 18.95/19.16          | (r1_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 18.95/19.16      inference('sup-', [status(thm)], ['49', '50'])).
% 18.95/19.16  thf('52', plain,
% 18.95/19.16      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 18.95/19.16        (k1_tops_1 @ sk_A @ sk_C))),
% 18.95/19.16      inference('sup-', [status(thm)], ['42', '51'])).
% 18.95/19.16  thf(t86_xboole_1, axiom,
% 18.95/19.16    (![A:$i,B:$i,C:$i]:
% 18.95/19.16     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 18.95/19.16       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 18.95/19.16  thf('53', plain,
% 18.95/19.16      (![X17 : $i, X18 : $i, X19 : $i]:
% 18.95/19.16         (~ (r1_tarski @ X17 @ X18)
% 18.95/19.16          | ~ (r1_xboole_0 @ X17 @ X19)
% 18.95/19.16          | (r1_tarski @ X17 @ (k4_xboole_0 @ X18 @ X19)))),
% 18.95/19.16      inference('cnf', [status(esa)], [t86_xboole_1])).
% 18.95/19.16  thf('54', plain,
% 18.95/19.16      (![X0 : $i]:
% 18.95/19.16         ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 18.95/19.16           (k4_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))
% 18.95/19.16          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 18.95/19.16               X0))),
% 18.95/19.16      inference('sup-', [status(thm)], ['52', '53'])).
% 18.95/19.16  thf('55', plain,
% 18.95/19.16      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 18.95/19.16        (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 18.95/19.16      inference('sup-', [status(thm)], ['35', '54'])).
% 18.95/19.16  thf('56', plain, ($false), inference('demod', [status(thm)], ['20', '55'])).
% 18.95/19.16  
% 18.95/19.16  % SZS output end Refutation
% 18.95/19.16  
% 18.95/19.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
