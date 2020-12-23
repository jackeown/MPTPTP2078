%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.okIQTGuA4P

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:03 EST 2020

% Result     : Theorem 56.60s
% Output     : Refutation 56.60s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 452 expanded)
%              Number of leaves         :   27 ( 150 expanded)
%              Depth                    :   21
%              Number of atoms          : 1620 (5138 expanded)
%              Number of equality atoms :   32 (  47 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X29 @ X28 ) @ X28 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
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
    ! [X25: $i,X27: $i] :
      ( ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( r1_tarski @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X29 @ X28 ) @ X28 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('26',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('27',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('28',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('29',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X19 @ X21 )
      | ( r1_tarski @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ ( k4_xboole_0 @ X3 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k4_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['27','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('39',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X25: $i,X27: $i] :
      ( ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( r1_tarski @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( r1_tarski @ X30 @ X32 )
      | ( r1_tarski @ ( k1_tops_1 @ X31 @ X30 ) @ ( k1_tops_1 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','47'])).

thf('49',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['23','24'])).

thf('56',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ X0 )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X25: $i,X27: $i] :
      ( ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( r1_tarski @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('60',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X29 @ X28 ) @ X28 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ X0 )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ sk_C ),
    inference('sup-',[status(thm)],['51','66'])).

thf('68',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('69',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('71',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('73',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
      | ~ ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k2_xboole_0 @ sk_C @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('77',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X29 @ X28 ) @ X28 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('81',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 )
      | ( r1_xboole_0 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ X1 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k2_xboole_0 @ sk_C @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['75','82'])).

thf('84',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X19 @ X21 )
      | ( r1_tarski @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_C @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['67','68'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('88',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('90',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X19 @ X21 )
      | ( r1_tarski @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('94',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('98',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X2 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('110',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('111',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 )
      | ( r1_xboole_0 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X19 @ X21 )
      | ( r1_tarski @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) @ ( k4_xboole_0 @ X3 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['108','115'])).

thf('117',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) )
      | ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['108','115'])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['103','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X19 @ X21 )
      | ( r1_tarski @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) @ ( k4_xboole_0 @ X3 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['122','127'])).

thf('129',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) )
      | ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
        = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('132',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('133',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( r1_xboole_0 @ X13 @ X16 )
      | ~ ( r1_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X19 @ X21 )
      | ( r1_tarski @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('136',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X3 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X2 @ X1 ) ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['131','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ ( k4_xboole_0 @ X3 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X2 @ X0 ) ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['130','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['121','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_C @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) )
      = ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['86','141'])).

thf('143',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['67','68'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_C @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) )
      = ( k4_xboole_0 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ X0 @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['85','144'])).

thf('146',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['50','145'])).

thf('147',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ X0 )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','148'])).

thf('150',plain,(
    $false ),
    inference(demod,[status(thm)],['20','149'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.okIQTGuA4P
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:54:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 56.60/56.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 56.60/56.85  % Solved by: fo/fo7.sh
% 56.60/56.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 56.60/56.85  % done 37944 iterations in 56.343s
% 56.60/56.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 56.60/56.85  % SZS output start Refutation
% 56.60/56.85  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 56.60/56.85  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 56.60/56.85  thf(sk_B_type, type, sk_B: $i).
% 56.60/56.85  thf(sk_C_type, type, sk_C: $i).
% 56.60/56.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 56.60/56.85  thf(sk_A_type, type, sk_A: $i).
% 56.60/56.85  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 56.60/56.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 56.60/56.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 56.60/56.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 56.60/56.85  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 56.60/56.85  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 56.60/56.85  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 56.60/56.85  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 56.60/56.85  thf(t50_tops_1, conjecture,
% 56.60/56.85    (![A:$i]:
% 56.60/56.85     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 56.60/56.85       ( ![B:$i]:
% 56.60/56.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 56.60/56.85           ( ![C:$i]:
% 56.60/56.85             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 56.60/56.85               ( r1_tarski @
% 56.60/56.85                 ( k1_tops_1 @
% 56.60/56.85                   A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 56.60/56.85                 ( k7_subset_1 @
% 56.60/56.85                   ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 56.60/56.85                   ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 56.60/56.85  thf(zf_stmt_0, negated_conjecture,
% 56.60/56.85    (~( ![A:$i]:
% 56.60/56.85        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 56.60/56.85          ( ![B:$i]:
% 56.60/56.85            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 56.60/56.85              ( ![C:$i]:
% 56.60/56.85                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 56.60/56.85                  ( r1_tarski @
% 56.60/56.85                    ( k1_tops_1 @
% 56.60/56.85                      A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 56.60/56.85                    ( k7_subset_1 @
% 56.60/56.85                      ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 56.60/56.85                      ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 56.60/56.85    inference('cnf.neg', [status(esa)], [t50_tops_1])).
% 56.60/56.85  thf('0', plain,
% 56.60/56.85      (~ (r1_tarski @ 
% 56.60/56.85          (k1_tops_1 @ sk_A @ 
% 56.60/56.85           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 56.60/56.85          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 56.60/56.85           (k1_tops_1 @ sk_A @ sk_C)))),
% 56.60/56.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.60/56.85  thf('1', plain,
% 56.60/56.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 56.60/56.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.60/56.85  thf(redefinition_k7_subset_1, axiom,
% 56.60/56.85    (![A:$i,B:$i,C:$i]:
% 56.60/56.85     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 56.60/56.85       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 56.60/56.85  thf('2', plain,
% 56.60/56.85      (![X22 : $i, X23 : $i, X24 : $i]:
% 56.60/56.85         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 56.60/56.85          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 56.60/56.85      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 56.60/56.85  thf('3', plain,
% 56.60/56.85      (![X0 : $i]:
% 56.60/56.85         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 56.60/56.85           = (k4_xboole_0 @ sk_B @ X0))),
% 56.60/56.85      inference('sup-', [status(thm)], ['1', '2'])).
% 56.60/56.85  thf('4', plain,
% 56.60/56.85      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 56.60/56.85          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 56.60/56.85           (k1_tops_1 @ sk_A @ sk_C)))),
% 56.60/56.85      inference('demod', [status(thm)], ['0', '3'])).
% 56.60/56.85  thf('5', plain,
% 56.60/56.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 56.60/56.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.60/56.85  thf(t3_subset, axiom,
% 56.60/56.85    (![A:$i,B:$i]:
% 56.60/56.85     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 56.60/56.85  thf('6', plain,
% 56.60/56.85      (![X25 : $i, X26 : $i]:
% 56.60/56.85         ((r1_tarski @ X25 @ X26) | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 56.60/56.85      inference('cnf', [status(esa)], [t3_subset])).
% 56.60/56.85  thf('7', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 56.60/56.85      inference('sup-', [status(thm)], ['5', '6'])).
% 56.60/56.85  thf('8', plain,
% 56.60/56.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 56.60/56.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.60/56.85  thf(t44_tops_1, axiom,
% 56.60/56.85    (![A:$i]:
% 56.60/56.85     ( ( l1_pre_topc @ A ) =>
% 56.60/56.85       ( ![B:$i]:
% 56.60/56.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 56.60/56.85           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 56.60/56.85  thf('9', plain,
% 56.60/56.85      (![X28 : $i, X29 : $i]:
% 56.60/56.85         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 56.60/56.85          | (r1_tarski @ (k1_tops_1 @ X29 @ X28) @ X28)
% 56.60/56.85          | ~ (l1_pre_topc @ X29))),
% 56.60/56.85      inference('cnf', [status(esa)], [t44_tops_1])).
% 56.60/56.85  thf('10', plain,
% 56.60/56.85      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 56.60/56.85      inference('sup-', [status(thm)], ['8', '9'])).
% 56.60/56.85  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 56.60/56.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.60/56.85  thf('12', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 56.60/56.85      inference('demod', [status(thm)], ['10', '11'])).
% 56.60/56.85  thf(t1_xboole_1, axiom,
% 56.60/56.85    (![A:$i,B:$i,C:$i]:
% 56.60/56.85     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 56.60/56.85       ( r1_tarski @ A @ C ) ))).
% 56.60/56.85  thf('13', plain,
% 56.60/56.85      (![X5 : $i, X6 : $i, X7 : $i]:
% 56.60/56.85         (~ (r1_tarski @ X5 @ X6)
% 56.60/56.85          | ~ (r1_tarski @ X6 @ X7)
% 56.60/56.85          | (r1_tarski @ X5 @ X7))),
% 56.60/56.85      inference('cnf', [status(esa)], [t1_xboole_1])).
% 56.60/56.85  thf('14', plain,
% 56.60/56.85      (![X0 : $i]:
% 56.60/56.85         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 56.60/56.85          | ~ (r1_tarski @ sk_B @ X0))),
% 56.60/56.85      inference('sup-', [status(thm)], ['12', '13'])).
% 56.60/56.85  thf('15', plain,
% 56.60/56.85      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 56.60/56.85      inference('sup-', [status(thm)], ['7', '14'])).
% 56.60/56.85  thf('16', plain,
% 56.60/56.85      (![X25 : $i, X27 : $i]:
% 56.60/56.85         ((m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X27)) | ~ (r1_tarski @ X25 @ X27))),
% 56.60/56.85      inference('cnf', [status(esa)], [t3_subset])).
% 56.60/56.85  thf('17', plain,
% 56.60/56.85      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 56.60/56.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 56.60/56.85      inference('sup-', [status(thm)], ['15', '16'])).
% 56.60/56.85  thf('18', plain,
% 56.60/56.85      (![X22 : $i, X23 : $i, X24 : $i]:
% 56.60/56.85         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 56.60/56.85          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 56.60/56.85      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 56.60/56.85  thf('19', plain,
% 56.60/56.85      (![X0 : $i]:
% 56.60/56.85         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 56.60/56.85           = (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 56.60/56.85      inference('sup-', [status(thm)], ['17', '18'])).
% 56.60/56.85  thf('20', plain,
% 56.60/56.85      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 56.60/56.85          (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 56.60/56.85      inference('demod', [status(thm)], ['4', '19'])).
% 56.60/56.85  thf('21', plain,
% 56.60/56.85      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 56.60/56.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.60/56.85  thf('22', plain,
% 56.60/56.85      (![X28 : $i, X29 : $i]:
% 56.60/56.85         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 56.60/56.85          | (r1_tarski @ (k1_tops_1 @ X29 @ X28) @ X28)
% 56.60/56.85          | ~ (l1_pre_topc @ X29))),
% 56.60/56.85      inference('cnf', [status(esa)], [t44_tops_1])).
% 56.60/56.85  thf('23', plain,
% 56.60/56.85      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 56.60/56.85      inference('sup-', [status(thm)], ['21', '22'])).
% 56.60/56.85  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 56.60/56.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.60/56.85  thf('25', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 56.60/56.85      inference('demod', [status(thm)], ['23', '24'])).
% 56.60/56.85  thf(t12_xboole_1, axiom,
% 56.60/56.85    (![A:$i,B:$i]:
% 56.60/56.85     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 56.60/56.85  thf('26', plain,
% 56.60/56.85      (![X3 : $i, X4 : $i]:
% 56.60/56.85         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 56.60/56.85      inference('cnf', [status(esa)], [t12_xboole_1])).
% 56.60/56.85  thf('27', plain,
% 56.60/56.85      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C) = (sk_C))),
% 56.60/56.85      inference('sup-', [status(thm)], ['25', '26'])).
% 56.60/56.85  thf(t36_xboole_1, axiom,
% 56.60/56.85    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 56.60/56.85  thf('28', plain,
% 56.60/56.85      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 56.60/56.85      inference('cnf', [status(esa)], [t36_xboole_1])).
% 56.60/56.85  thf(t79_xboole_1, axiom,
% 56.60/56.85    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 56.60/56.85  thf('29', plain,
% 56.60/56.85      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X18)),
% 56.60/56.85      inference('cnf', [status(esa)], [t79_xboole_1])).
% 56.60/56.85  thf(t70_xboole_1, axiom,
% 56.60/56.85    (![A:$i,B:$i,C:$i]:
% 56.60/56.85     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 56.60/56.85            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 56.60/56.85       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 56.60/56.85            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 56.60/56.85  thf('30', plain,
% 56.60/56.85      (![X13 : $i, X14 : $i, X16 : $i]:
% 56.60/56.85         ((r1_xboole_0 @ X13 @ X14)
% 56.60/56.85          | ~ (r1_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X16)))),
% 56.60/56.85      inference('cnf', [status(esa)], [t70_xboole_1])).
% 56.60/56.85  thf('31', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         (r1_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)),
% 56.60/56.85      inference('sup-', [status(thm)], ['29', '30'])).
% 56.60/56.85  thf(t86_xboole_1, axiom,
% 56.60/56.85    (![A:$i,B:$i,C:$i]:
% 56.60/56.85     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 56.60/56.85       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 56.60/56.85  thf('32', plain,
% 56.60/56.85      (![X19 : $i, X20 : $i, X21 : $i]:
% 56.60/56.85         (~ (r1_tarski @ X19 @ X20)
% 56.60/56.85          | ~ (r1_xboole_0 @ X19 @ X21)
% 56.60/56.85          | (r1_tarski @ X19 @ (k4_xboole_0 @ X20 @ X21)))),
% 56.60/56.85      inference('cnf', [status(esa)], [t86_xboole_1])).
% 56.60/56.85  thf('33', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 56.60/56.85         ((r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)) @ 
% 56.60/56.85           (k4_xboole_0 @ X3 @ X0))
% 56.60/56.85          | ~ (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)) @ X3))),
% 56.60/56.85      inference('sup-', [status(thm)], ['31', '32'])).
% 56.60/56.85  thf('34', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         (r1_tarski @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1)) @ 
% 56.60/56.85          (k4_xboole_0 @ X0 @ X2))),
% 56.60/56.85      inference('sup-', [status(thm)], ['28', '33'])).
% 56.60/56.85  thf('35', plain,
% 56.60/56.85      (![X0 : $i]:
% 56.60/56.85         (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C) @ 
% 56.60/56.85          (k4_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 56.60/56.85      inference('sup+', [status(thm)], ['27', '34'])).
% 56.60/56.85  thf('36', plain,
% 56.60/56.85      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 56.60/56.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.60/56.85  thf('37', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 56.60/56.85      inference('sup-', [status(thm)], ['5', '6'])).
% 56.60/56.85  thf('38', plain,
% 56.60/56.85      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 56.60/56.85      inference('cnf', [status(esa)], [t36_xboole_1])).
% 56.60/56.85  thf('39', plain,
% 56.60/56.85      (![X5 : $i, X6 : $i, X7 : $i]:
% 56.60/56.85         (~ (r1_tarski @ X5 @ X6)
% 56.60/56.85          | ~ (r1_tarski @ X6 @ X7)
% 56.60/56.85          | (r1_tarski @ X5 @ X7))),
% 56.60/56.85      inference('cnf', [status(esa)], [t1_xboole_1])).
% 56.60/56.85  thf('40', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 56.60/56.85      inference('sup-', [status(thm)], ['38', '39'])).
% 56.60/56.85  thf('41', plain,
% 56.60/56.85      (![X0 : $i]:
% 56.60/56.85         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 56.60/56.85      inference('sup-', [status(thm)], ['37', '40'])).
% 56.60/56.85  thf('42', plain,
% 56.60/56.85      (![X25 : $i, X27 : $i]:
% 56.60/56.85         ((m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X27)) | ~ (r1_tarski @ X25 @ X27))),
% 56.60/56.85      inference('cnf', [status(esa)], [t3_subset])).
% 56.60/56.85  thf('43', plain,
% 56.60/56.85      (![X0 : $i]:
% 56.60/56.85         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 56.60/56.85          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 56.60/56.85      inference('sup-', [status(thm)], ['41', '42'])).
% 56.60/56.85  thf(t48_tops_1, axiom,
% 56.60/56.85    (![A:$i]:
% 56.60/56.85     ( ( l1_pre_topc @ A ) =>
% 56.60/56.85       ( ![B:$i]:
% 56.60/56.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 56.60/56.85           ( ![C:$i]:
% 56.60/56.85             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 56.60/56.85               ( ( r1_tarski @ B @ C ) =>
% 56.60/56.85                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 56.60/56.85  thf('44', plain,
% 56.60/56.85      (![X30 : $i, X31 : $i, X32 : $i]:
% 56.60/56.85         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 56.60/56.85          | ~ (r1_tarski @ X30 @ X32)
% 56.60/56.85          | (r1_tarski @ (k1_tops_1 @ X31 @ X30) @ (k1_tops_1 @ X31 @ X32))
% 56.60/56.85          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 56.60/56.85          | ~ (l1_pre_topc @ X31))),
% 56.60/56.85      inference('cnf', [status(esa)], [t48_tops_1])).
% 56.60/56.85  thf('45', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i]:
% 56.60/56.85         (~ (l1_pre_topc @ sk_A)
% 56.60/56.85          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 56.60/56.85          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 56.60/56.85             (k1_tops_1 @ sk_A @ X1))
% 56.60/56.85          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 56.60/56.85      inference('sup-', [status(thm)], ['43', '44'])).
% 56.60/56.85  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 56.60/56.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.60/56.85  thf('47', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i]:
% 56.60/56.85         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 56.60/56.85          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 56.60/56.85             (k1_tops_1 @ sk_A @ X1))
% 56.60/56.85          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 56.60/56.85      inference('demod', [status(thm)], ['45', '46'])).
% 56.60/56.85  thf('48', plain,
% 56.60/56.85      (![X0 : $i]:
% 56.60/56.85         (~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_B)
% 56.60/56.85          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 56.60/56.85             (k1_tops_1 @ sk_A @ sk_B)))),
% 56.60/56.85      inference('sup-', [status(thm)], ['36', '47'])).
% 56.60/56.85  thf('49', plain,
% 56.60/56.85      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 56.60/56.85      inference('cnf', [status(esa)], [t36_xboole_1])).
% 56.60/56.85  thf('50', plain,
% 56.60/56.85      (![X0 : $i]:
% 56.60/56.85         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 56.60/56.85          (k1_tops_1 @ sk_A @ sk_B))),
% 56.60/56.85      inference('demod', [status(thm)], ['48', '49'])).
% 56.60/56.85  thf('51', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 56.60/56.85      inference('demod', [status(thm)], ['23', '24'])).
% 56.60/56.85  thf('52', plain,
% 56.60/56.85      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 56.60/56.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.60/56.85  thf('53', plain,
% 56.60/56.85      (![X25 : $i, X26 : $i]:
% 56.60/56.85         ((r1_tarski @ X25 @ X26) | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 56.60/56.85      inference('cnf', [status(esa)], [t3_subset])).
% 56.60/56.85  thf('54', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 56.60/56.85      inference('sup-', [status(thm)], ['52', '53'])).
% 56.60/56.85  thf('55', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 56.60/56.85      inference('demod', [status(thm)], ['23', '24'])).
% 56.60/56.85  thf('56', plain,
% 56.60/56.85      (![X5 : $i, X6 : $i, X7 : $i]:
% 56.60/56.85         (~ (r1_tarski @ X5 @ X6)
% 56.60/56.85          | ~ (r1_tarski @ X6 @ X7)
% 56.60/56.85          | (r1_tarski @ X5 @ X7))),
% 56.60/56.85      inference('cnf', [status(esa)], [t1_xboole_1])).
% 56.60/56.85  thf('57', plain,
% 56.60/56.85      (![X0 : $i]:
% 56.60/56.85         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ X0)
% 56.60/56.85          | ~ (r1_tarski @ sk_C @ X0))),
% 56.60/56.85      inference('sup-', [status(thm)], ['55', '56'])).
% 56.60/56.85  thf('58', plain,
% 56.60/56.85      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))),
% 56.60/56.85      inference('sup-', [status(thm)], ['54', '57'])).
% 56.60/56.85  thf('59', plain,
% 56.60/56.85      (![X25 : $i, X27 : $i]:
% 56.60/56.85         ((m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X27)) | ~ (r1_tarski @ X25 @ X27))),
% 56.60/56.85      inference('cnf', [status(esa)], [t3_subset])).
% 56.60/56.85  thf('60', plain,
% 56.60/56.85      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 56.60/56.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 56.60/56.85      inference('sup-', [status(thm)], ['58', '59'])).
% 56.60/56.85  thf('61', plain,
% 56.60/56.85      (![X28 : $i, X29 : $i]:
% 56.60/56.85         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 56.60/56.85          | (r1_tarski @ (k1_tops_1 @ X29 @ X28) @ X28)
% 56.60/56.85          | ~ (l1_pre_topc @ X29))),
% 56.60/56.85      inference('cnf', [status(esa)], [t44_tops_1])).
% 56.60/56.85  thf('62', plain,
% 56.60/56.85      ((~ (l1_pre_topc @ sk_A)
% 56.60/56.85        | (r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 56.60/56.85           (k1_tops_1 @ sk_A @ sk_C)))),
% 56.60/56.85      inference('sup-', [status(thm)], ['60', '61'])).
% 56.60/56.85  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 56.60/56.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.60/56.85  thf('64', plain,
% 56.60/56.85      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 56.60/56.85        (k1_tops_1 @ sk_A @ sk_C))),
% 56.60/56.85      inference('demod', [status(thm)], ['62', '63'])).
% 56.60/56.85  thf('65', plain,
% 56.60/56.85      (![X5 : $i, X6 : $i, X7 : $i]:
% 56.60/56.85         (~ (r1_tarski @ X5 @ X6)
% 56.60/56.85          | ~ (r1_tarski @ X6 @ X7)
% 56.60/56.85          | (r1_tarski @ X5 @ X7))),
% 56.60/56.85      inference('cnf', [status(esa)], [t1_xboole_1])).
% 56.60/56.85  thf('66', plain,
% 56.60/56.85      (![X0 : $i]:
% 56.60/56.85         ((r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ X0)
% 56.60/56.85          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ X0))),
% 56.60/56.85      inference('sup-', [status(thm)], ['64', '65'])).
% 56.60/56.85  thf('67', plain,
% 56.60/56.85      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ sk_C)),
% 56.60/56.85      inference('sup-', [status(thm)], ['51', '66'])).
% 56.60/56.85  thf('68', plain,
% 56.60/56.85      (![X3 : $i, X4 : $i]:
% 56.60/56.85         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 56.60/56.85      inference('cnf', [status(esa)], [t12_xboole_1])).
% 56.60/56.85  thf('69', plain,
% 56.60/56.85      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ sk_C)
% 56.60/56.85         = (sk_C))),
% 56.60/56.85      inference('sup-', [status(thm)], ['67', '68'])).
% 56.60/56.85  thf('70', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         (r1_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)),
% 56.60/56.85      inference('sup-', [status(thm)], ['29', '30'])).
% 56.60/56.85  thf('71', plain,
% 56.60/56.85      (![X0 : $i]:
% 56.60/56.85         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ 
% 56.60/56.85          (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))),
% 56.60/56.85      inference('sup+', [status(thm)], ['69', '70'])).
% 56.60/56.85  thf('72', plain,
% 56.60/56.85      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X18)),
% 56.60/56.85      inference('cnf', [status(esa)], [t79_xboole_1])).
% 56.60/56.85  thf('73', plain,
% 56.60/56.85      (![X13 : $i, X14 : $i, X15 : $i]:
% 56.60/56.85         ((r1_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 56.60/56.85          | ~ (r1_xboole_0 @ X13 @ X14)
% 56.60/56.85          | ~ (r1_xboole_0 @ X13 @ X15))),
% 56.60/56.85      inference('cnf', [status(esa)], [t70_xboole_1])).
% 56.60/56.85  thf('74', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         (~ (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 56.60/56.85          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 56.60/56.85      inference('sup-', [status(thm)], ['72', '73'])).
% 56.60/56.85  thf('75', plain,
% 56.60/56.85      (![X0 : $i]:
% 56.60/56.85         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ 
% 56.60/56.85          (k2_xboole_0 @ sk_C @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))),
% 56.60/56.85      inference('sup-', [status(thm)], ['71', '74'])).
% 56.60/56.85  thf('76', plain,
% 56.60/56.85      (![X0 : $i]:
% 56.60/56.85         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 56.60/56.85          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 56.60/56.85      inference('sup-', [status(thm)], ['41', '42'])).
% 56.60/56.85  thf('77', plain,
% 56.60/56.85      (![X28 : $i, X29 : $i]:
% 56.60/56.85         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 56.60/56.85          | (r1_tarski @ (k1_tops_1 @ X29 @ X28) @ X28)
% 56.60/56.85          | ~ (l1_pre_topc @ X29))),
% 56.60/56.85      inference('cnf', [status(esa)], [t44_tops_1])).
% 56.60/56.85  thf('78', plain,
% 56.60/56.85      (![X0 : $i]:
% 56.60/56.85         (~ (l1_pre_topc @ sk_A)
% 56.60/56.85          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 56.60/56.85             (k4_xboole_0 @ sk_B @ X0)))),
% 56.60/56.85      inference('sup-', [status(thm)], ['76', '77'])).
% 56.60/56.85  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 56.60/56.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 56.60/56.85  thf('80', plain,
% 56.60/56.85      (![X0 : $i]:
% 56.60/56.85         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 56.60/56.85          (k4_xboole_0 @ sk_B @ X0))),
% 56.60/56.85      inference('demod', [status(thm)], ['78', '79'])).
% 56.60/56.85  thf(t63_xboole_1, axiom,
% 56.60/56.85    (![A:$i,B:$i,C:$i]:
% 56.60/56.85     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 56.60/56.85       ( r1_xboole_0 @ A @ C ) ))).
% 56.60/56.85  thf('81', plain,
% 56.60/56.85      (![X10 : $i, X11 : $i, X12 : $i]:
% 56.60/56.85         (~ (r1_tarski @ X10 @ X11)
% 56.60/56.85          | ~ (r1_xboole_0 @ X11 @ X12)
% 56.60/56.85          | (r1_xboole_0 @ X10 @ X12))),
% 56.60/56.85      inference('cnf', [status(esa)], [t63_xboole_1])).
% 56.60/56.85  thf('82', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i]:
% 56.60/56.85         ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ X1)
% 56.60/56.85          | ~ (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 56.60/56.85      inference('sup-', [status(thm)], ['80', '81'])).
% 56.60/56.85  thf('83', plain,
% 56.60/56.85      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 56.60/56.85        (k2_xboole_0 @ sk_C @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))),
% 56.60/56.85      inference('sup-', [status(thm)], ['75', '82'])).
% 56.60/56.85  thf('84', plain,
% 56.60/56.85      (![X19 : $i, X20 : $i, X21 : $i]:
% 56.60/56.85         (~ (r1_tarski @ X19 @ X20)
% 56.60/56.85          | ~ (r1_xboole_0 @ X19 @ X21)
% 56.60/56.85          | (r1_tarski @ X19 @ (k4_xboole_0 @ X20 @ X21)))),
% 56.60/56.85      inference('cnf', [status(esa)], [t86_xboole_1])).
% 56.60/56.85  thf('85', plain,
% 56.60/56.85      (![X0 : $i]:
% 56.60/56.85         ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 56.60/56.85           (k4_xboole_0 @ X0 @ 
% 56.60/56.85            (k2_xboole_0 @ sk_C @ 
% 56.60/56.85             (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)))))
% 56.60/56.85          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 56.60/56.85               X0))),
% 56.60/56.85      inference('sup-', [status(thm)], ['83', '84'])).
% 56.60/56.85  thf('86', plain,
% 56.60/56.85      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ sk_C)
% 56.60/56.85         = (sk_C))),
% 56.60/56.85      inference('sup-', [status(thm)], ['67', '68'])).
% 56.60/56.85  thf(d10_xboole_0, axiom,
% 56.60/56.85    (![A:$i,B:$i]:
% 56.60/56.85     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 56.60/56.85  thf('87', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 56.60/56.85      inference('cnf', [status(esa)], [d10_xboole_0])).
% 56.60/56.85  thf('88', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 56.60/56.85      inference('simplify', [status(thm)], ['87'])).
% 56.60/56.85  thf('89', plain,
% 56.60/56.85      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X18)),
% 56.60/56.85      inference('cnf', [status(esa)], [t79_xboole_1])).
% 56.60/56.85  thf('90', plain,
% 56.60/56.85      (![X19 : $i, X20 : $i, X21 : $i]:
% 56.60/56.85         (~ (r1_tarski @ X19 @ X20)
% 56.60/56.85          | ~ (r1_xboole_0 @ X19 @ X21)
% 56.60/56.85          | (r1_tarski @ X19 @ (k4_xboole_0 @ X20 @ X21)))),
% 56.60/56.85      inference('cnf', [status(esa)], [t86_xboole_1])).
% 56.60/56.85  thf('91', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X0))
% 56.60/56.85          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 56.60/56.85      inference('sup-', [status(thm)], ['89', '90'])).
% 56.60/56.85  thf('92', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i]:
% 56.60/56.85         (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ 
% 56.60/56.85          (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 56.60/56.85      inference('sup-', [status(thm)], ['88', '91'])).
% 56.60/56.85  thf('93', plain,
% 56.60/56.85      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 56.60/56.85      inference('cnf', [status(esa)], [t36_xboole_1])).
% 56.60/56.85  thf('94', plain,
% 56.60/56.85      (![X0 : $i, X2 : $i]:
% 56.60/56.85         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 56.60/56.85      inference('cnf', [status(esa)], [d10_xboole_0])).
% 56.60/56.85  thf('95', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i]:
% 56.60/56.85         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 56.60/56.85          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 56.60/56.85      inference('sup-', [status(thm)], ['93', '94'])).
% 56.60/56.85  thf('96', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i]:
% 56.60/56.85         ((k4_xboole_0 @ X1 @ X0)
% 56.60/56.85           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 56.60/56.85      inference('sup-', [status(thm)], ['92', '95'])).
% 56.60/56.85  thf('97', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         (r1_tarski @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1)) @ 
% 56.60/56.85          (k4_xboole_0 @ X0 @ X2))),
% 56.60/56.85      inference('sup-', [status(thm)], ['28', '33'])).
% 56.60/56.85  thf('98', plain,
% 56.60/56.85      (![X0 : $i, X2 : $i]:
% 56.60/56.85         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 56.60/56.85      inference('cnf', [status(esa)], [d10_xboole_0])).
% 56.60/56.85  thf('99', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         (~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ 
% 56.60/56.85             (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2)))
% 56.60/56.85          | ((k4_xboole_0 @ X1 @ X0)
% 56.60/56.85              = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X2))))),
% 56.60/56.85      inference('sup-', [status(thm)], ['97', '98'])).
% 56.60/56.85  thf('100', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         (~ (r1_tarski @ 
% 56.60/56.85             (k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1) @ 
% 56.60/56.85             (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 56.60/56.85          | ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)
% 56.60/56.85              = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 56.60/56.85                 (k2_xboole_0 @ X1 @ X0))))),
% 56.60/56.85      inference('sup-', [status(thm)], ['96', '99'])).
% 56.60/56.85  thf('101', plain,
% 56.60/56.85      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 56.60/56.85      inference('cnf', [status(esa)], [t36_xboole_1])).
% 56.60/56.85  thf('102', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i]:
% 56.60/56.85         ((k4_xboole_0 @ X1 @ X0)
% 56.60/56.85           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 56.60/56.85      inference('sup-', [status(thm)], ['92', '95'])).
% 56.60/56.85  thf('103', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)
% 56.60/56.85           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 56.60/56.85      inference('demod', [status(thm)], ['100', '101', '102'])).
% 56.60/56.85  thf('104', plain,
% 56.60/56.85      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 56.60/56.85      inference('cnf', [status(esa)], [t36_xboole_1])).
% 56.60/56.85  thf('105', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 56.60/56.85      inference('sup-', [status(thm)], ['38', '39'])).
% 56.60/56.85  thf('106', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2) @ X0)),
% 56.60/56.85      inference('sup-', [status(thm)], ['104', '105'])).
% 56.60/56.85  thf('107', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X2 @ X0))
% 56.60/56.85          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 56.60/56.85      inference('sup-', [status(thm)], ['89', '90'])).
% 56.60/56.85  thf('108', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1) @ 
% 56.60/56.85          (k4_xboole_0 @ X0 @ X1))),
% 56.60/56.85      inference('sup-', [status(thm)], ['106', '107'])).
% 56.60/56.85  thf('109', plain,
% 56.60/56.85      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X18)),
% 56.60/56.85      inference('cnf', [status(esa)], [t79_xboole_1])).
% 56.60/56.85  thf('110', plain,
% 56.60/56.85      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 56.60/56.85      inference('cnf', [status(esa)], [t36_xboole_1])).
% 56.60/56.85  thf('111', plain,
% 56.60/56.85      (![X10 : $i, X11 : $i, X12 : $i]:
% 56.60/56.85         (~ (r1_tarski @ X10 @ X11)
% 56.60/56.85          | ~ (r1_xboole_0 @ X11 @ X12)
% 56.60/56.85          | (r1_xboole_0 @ X10 @ X12))),
% 56.60/56.85      inference('cnf', [status(esa)], [t63_xboole_1])).
% 56.60/56.85  thf('112', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         ((r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 56.60/56.85          | ~ (r1_xboole_0 @ X0 @ X2))),
% 56.60/56.85      inference('sup-', [status(thm)], ['110', '111'])).
% 56.60/56.85  thf('113', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         (r1_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0)),
% 56.60/56.85      inference('sup-', [status(thm)], ['109', '112'])).
% 56.60/56.85  thf('114', plain,
% 56.60/56.85      (![X19 : $i, X20 : $i, X21 : $i]:
% 56.60/56.85         (~ (r1_tarski @ X19 @ X20)
% 56.60/56.85          | ~ (r1_xboole_0 @ X19 @ X21)
% 56.60/56.85          | (r1_tarski @ X19 @ (k4_xboole_0 @ X20 @ X21)))),
% 56.60/56.85      inference('cnf', [status(esa)], [t86_xboole_1])).
% 56.60/56.85  thf('115', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 56.60/56.85         ((r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1) @ 
% 56.60/56.85           (k4_xboole_0 @ X3 @ X0))
% 56.60/56.85          | ~ (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1) @ X3))),
% 56.60/56.85      inference('sup-', [status(thm)], ['113', '114'])).
% 56.60/56.85  thf('116', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ X0) @ 
% 56.60/56.85          (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 56.60/56.85      inference('sup-', [status(thm)], ['108', '115'])).
% 56.60/56.85  thf('117', plain,
% 56.60/56.85      (![X0 : $i, X2 : $i]:
% 56.60/56.85         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 56.60/56.85      inference('cnf', [status(esa)], [d10_xboole_0])).
% 56.60/56.85  thf('118', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         (~ (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ 
% 56.60/56.85             (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1))
% 56.60/56.85          | ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 56.60/56.85              = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)))),
% 56.60/56.85      inference('sup-', [status(thm)], ['116', '117'])).
% 56.60/56.85  thf('119', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ X0) @ 
% 56.60/56.85          (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 56.60/56.85      inference('sup-', [status(thm)], ['108', '115'])).
% 56.60/56.85  thf('120', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0)
% 56.60/56.85           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 56.60/56.85      inference('demod', [status(thm)], ['118', '119'])).
% 56.60/56.85  thf('121', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 56.60/56.85           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 56.60/56.85      inference('demod', [status(thm)], ['103', '120'])).
% 56.60/56.85  thf('122', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2) @ X0)),
% 56.60/56.85      inference('sup-', [status(thm)], ['104', '105'])).
% 56.60/56.85  thf('123', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         (r1_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0)),
% 56.60/56.85      inference('sup-', [status(thm)], ['109', '112'])).
% 56.60/56.85  thf('124', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         (~ (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 56.60/56.85          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2)))),
% 56.60/56.85      inference('sup-', [status(thm)], ['72', '73'])).
% 56.60/56.85  thf('125', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         (r1_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1) @ 
% 56.60/56.85          (k2_xboole_0 @ X1 @ X0))),
% 56.60/56.85      inference('sup-', [status(thm)], ['123', '124'])).
% 56.60/56.85  thf('126', plain,
% 56.60/56.85      (![X19 : $i, X20 : $i, X21 : $i]:
% 56.60/56.85         (~ (r1_tarski @ X19 @ X20)
% 56.60/56.85          | ~ (r1_xboole_0 @ X19 @ X21)
% 56.60/56.85          | (r1_tarski @ X19 @ (k4_xboole_0 @ X20 @ X21)))),
% 56.60/56.85      inference('cnf', [status(esa)], [t86_xboole_1])).
% 56.60/56.85  thf('127', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 56.60/56.85         ((r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1) @ 
% 56.60/56.85           (k4_xboole_0 @ X3 @ (k2_xboole_0 @ X1 @ X0)))
% 56.60/56.85          | ~ (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1) @ X3))),
% 56.60/56.85      inference('sup-', [status(thm)], ['125', '126'])).
% 56.60/56.85  thf('128', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X1) @ 
% 56.60/56.85          (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X2)))),
% 56.60/56.85      inference('sup-', [status(thm)], ['122', '127'])).
% 56.60/56.85  thf('129', plain,
% 56.60/56.85      (![X0 : $i, X2 : $i]:
% 56.60/56.85         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 56.60/56.85      inference('cnf', [status(esa)], [d10_xboole_0])).
% 56.60/56.85  thf('130', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         (~ (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 56.60/56.85             (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1))
% 56.60/56.85          | ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 56.60/56.85              = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)))),
% 56.60/56.85      inference('sup-', [status(thm)], ['128', '129'])).
% 56.60/56.85  thf('131', plain,
% 56.60/56.85      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 56.60/56.85      inference('cnf', [status(esa)], [t36_xboole_1])).
% 56.60/56.85  thf('132', plain,
% 56.60/56.85      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X18)),
% 56.60/56.85      inference('cnf', [status(esa)], [t79_xboole_1])).
% 56.60/56.85  thf('133', plain,
% 56.60/56.85      (![X13 : $i, X14 : $i, X16 : $i]:
% 56.60/56.85         ((r1_xboole_0 @ X13 @ X16)
% 56.60/56.85          | ~ (r1_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X16)))),
% 56.60/56.85      inference('cnf', [status(esa)], [t70_xboole_1])).
% 56.60/56.85  thf('134', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         (r1_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X0)),
% 56.60/56.85      inference('sup-', [status(thm)], ['132', '133'])).
% 56.60/56.85  thf('135', plain,
% 56.60/56.85      (![X19 : $i, X20 : $i, X21 : $i]:
% 56.60/56.85         (~ (r1_tarski @ X19 @ X20)
% 56.60/56.85          | ~ (r1_xboole_0 @ X19 @ X21)
% 56.60/56.85          | (r1_tarski @ X19 @ (k4_xboole_0 @ X20 @ X21)))),
% 56.60/56.85      inference('cnf', [status(esa)], [t86_xboole_1])).
% 56.60/56.85  thf('136', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 56.60/56.85         ((r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 56.60/56.85           (k4_xboole_0 @ X3 @ X0))
% 56.60/56.85          | ~ (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3))),
% 56.60/56.85      inference('sup-', [status(thm)], ['134', '135'])).
% 56.60/56.85  thf('137', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         (r1_tarski @ (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X2 @ X1)) @ 
% 56.60/56.85          (k4_xboole_0 @ X0 @ X1))),
% 56.60/56.85      inference('sup-', [status(thm)], ['131', '136'])).
% 56.60/56.85  thf('138', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 56.60/56.85         ((r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)) @ 
% 56.60/56.85           (k4_xboole_0 @ X3 @ X0))
% 56.60/56.85          | ~ (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1)) @ X3))),
% 56.60/56.85      inference('sup-', [status(thm)], ['31', '32'])).
% 56.60/56.85  thf('139', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         (r1_tarski @ (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X2 @ X0)) @ 
% 56.60/56.85          (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 56.60/56.85      inference('sup-', [status(thm)], ['137', '138'])).
% 56.60/56.85  thf('140', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 56.60/56.85           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 56.60/56.85      inference('demod', [status(thm)], ['130', '139'])).
% 56.60/56.85  thf('141', plain,
% 56.60/56.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 56.60/56.85         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))
% 56.60/56.85           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 56.60/56.85      inference('demod', [status(thm)], ['121', '140'])).
% 56.60/56.85  thf('142', plain,
% 56.60/56.85      (![X0 : $i]:
% 56.60/56.85         ((k4_xboole_0 @ X0 @ 
% 56.60/56.85           (k2_xboole_0 @ sk_C @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))
% 56.60/56.85           = (k4_xboole_0 @ X0 @ 
% 56.60/56.85              (k2_xboole_0 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 56.60/56.85               sk_C)))),
% 56.60/56.85      inference('sup+', [status(thm)], ['86', '141'])).
% 56.60/56.85  thf('143', plain,
% 56.60/56.85      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ sk_C)
% 56.60/56.85         = (sk_C))),
% 56.60/56.85      inference('sup-', [status(thm)], ['67', '68'])).
% 56.60/56.85  thf('144', plain,
% 56.60/56.85      (![X0 : $i]:
% 56.60/56.85         ((k4_xboole_0 @ X0 @ 
% 56.60/56.85           (k2_xboole_0 @ sk_C @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C))))
% 56.60/56.85           = (k4_xboole_0 @ X0 @ sk_C))),
% 56.60/56.85      inference('demod', [status(thm)], ['142', '143'])).
% 56.60/56.85  thf('145', plain,
% 56.60/56.85      (![X0 : $i]:
% 56.60/56.85         ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 56.60/56.85           (k4_xboole_0 @ X0 @ sk_C))
% 56.60/56.85          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 56.60/56.85               X0))),
% 56.60/56.85      inference('demod', [status(thm)], ['85', '144'])).
% 56.60/56.85  thf('146', plain,
% 56.60/56.85      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 56.60/56.85        (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_C))),
% 56.60/56.85      inference('sup-', [status(thm)], ['50', '145'])).
% 56.60/56.85  thf('147', plain,
% 56.60/56.85      (![X5 : $i, X6 : $i, X7 : $i]:
% 56.60/56.85         (~ (r1_tarski @ X5 @ X6)
% 56.60/56.85          | ~ (r1_tarski @ X6 @ X7)
% 56.60/56.85          | (r1_tarski @ X5 @ X7))),
% 56.60/56.85      inference('cnf', [status(esa)], [t1_xboole_1])).
% 56.60/56.85  thf('148', plain,
% 56.60/56.85      (![X0 : $i]:
% 56.60/56.85         ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ X0)
% 56.60/56.85          | ~ (r1_tarski @ (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_C) @ 
% 56.60/56.85               X0))),
% 56.60/56.85      inference('sup-', [status(thm)], ['146', '147'])).
% 56.60/56.85  thf('149', plain,
% 56.60/56.85      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 56.60/56.85        (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 56.60/56.85      inference('sup-', [status(thm)], ['35', '148'])).
% 56.60/56.85  thf('150', plain, ($false), inference('demod', [status(thm)], ['20', '149'])).
% 56.60/56.85  
% 56.60/56.85  % SZS output end Refutation
% 56.60/56.85  
% 56.60/56.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
