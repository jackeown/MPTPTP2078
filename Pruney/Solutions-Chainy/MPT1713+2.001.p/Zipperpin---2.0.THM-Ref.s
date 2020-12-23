%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ej3OEwUX8m

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 233 expanded)
%              Number of leaves         :   27 (  78 expanded)
%              Depth                    :   21
%              Number of atoms          :  637 (2497 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('1',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('2',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('4',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(t22_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( m1_pre_topc @ B @ C )
               => ( ~ ( r1_tsep_1 @ B @ C )
                  & ~ ( r1_tsep_1 @ C @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( m1_pre_topc @ C @ A ) )
               => ( ( m1_pre_topc @ B @ C )
                 => ( ~ ( r1_tsep_1 @ B @ C )
                    & ~ ( r1_tsep_1 @ C @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t22_tmap_1])).

thf('5',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_C )
    | ( r1_tsep_1 @ sk_C @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B_1 )
   <= ( r1_tsep_1 @ sk_C @ sk_B_1 ) ),
    inference(split,[status(esa)],['5'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_struct_0 @ X22 )
      | ~ ( l1_struct_0 @ X23 )
      | ( r1_tsep_1 @ X23 @ X22 )
      | ~ ( r1_tsep_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('8',plain,
    ( ( ( r1_tsep_1 @ sk_B_1 @ sk_C )
      | ~ ( l1_struct_0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B_1 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( l1_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_tsep_1 @ sk_B_1 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B_1 ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_tsep_1 @ sk_B_1 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','15'])).

thf('17',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( l1_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_C )
   <= ( r1_tsep_1 @ sk_C @ sk_B_1 ) ),
    inference(demod,[status(thm)],['16','21'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('23',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( r1_tsep_1 @ X21 @ X20 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('24',plain,
    ( ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('27',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B_1 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('30',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_C @ sk_B_1 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
              <=> ( m1_pre_topc @ B @ C ) ) ) ) ) )).

thf('33',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ~ ( m1_pre_topc @ X24 @ X26 )
      | ( r1_tarski @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_pre_topc @ X26 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t4_tsep_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ~ ( m1_pre_topc @ sk_B_1 @ sk_C )
    | ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    m1_pre_topc @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('41',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ X6 @ ( k2_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('43',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) )
      | ~ ( r1_xboole_0 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ X0 )
   <= ( r1_tsep_1 @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['30','44'])).

thf('46',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('47',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('48',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('49',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_C )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf('50',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( r1_tsep_1 @ X21 @ X20 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('51',plain,
    ( ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('54',plain,
    ( ( ~ ( l1_struct_0 @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ~ ( l1_pre_topc @ sk_C )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_C ),
    inference(demod,[status(thm)],['19','20'])).

thf('57',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ X0 )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('60',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('61',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('64',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('65',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ~ ( l1_struct_0 @ sk_B_1 )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['46','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('70',plain,(
    ~ ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( r1_tsep_1 @ sk_C @ sk_B_1 )
    | ( r1_tsep_1 @ sk_B_1 @ sk_C ) ),
    inference(split,[status(esa)],['5'])).

thf('72',plain,(
    r1_tsep_1 @ sk_C @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ X0 ) ),
    inference(simpl_trail,[status(thm)],['45','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('75',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['80','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ej3OEwUX8m
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:00:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 105 iterations in 0.057s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.48  thf(dt_l1_pre_topc, axiom,
% 0.21/0.48    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.48  thf('0', plain, (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('1', plain, (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('2', plain, (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('3', plain, (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('4', plain, (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf(t22_tmap_1, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.48               ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.48                 ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.48            ( l1_pre_topc @ A ) ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.48              ( ![C:$i]:
% 0.21/0.48                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.48                  ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.48                    ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t22_tmap_1])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (((r1_tsep_1 @ sk_B_1 @ sk_C) | (r1_tsep_1 @ sk_C @ sk_B_1))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (((r1_tsep_1 @ sk_C @ sk_B_1)) <= (((r1_tsep_1 @ sk_C @ sk_B_1)))),
% 0.21/0.48      inference('split', [status(esa)], ['5'])).
% 0.21/0.48  thf(symmetry_r1_tsep_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.21/0.48       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X22 : $i, X23 : $i]:
% 0.21/0.48         (~ (l1_struct_0 @ X22)
% 0.21/0.48          | ~ (l1_struct_0 @ X23)
% 0.21/0.48          | (r1_tsep_1 @ X23 @ X22)
% 0.21/0.48          | ~ (r1_tsep_1 @ X22 @ X23))),
% 0.21/0.48      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      ((((r1_tsep_1 @ sk_B_1 @ sk_C)
% 0.21/0.48         | ~ (l1_struct_0 @ sk_B_1)
% 0.21/0.48         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (((~ (l1_pre_topc @ sk_B_1)
% 0.21/0.48         | ~ (l1_struct_0 @ sk_C)
% 0.21/0.48         | (r1_tsep_1 @ sk_B_1 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '8'])).
% 0.21/0.48  thf('10', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(dt_m1_pre_topc, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_pre_topc @ A ) =>
% 0.21/0.48       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X17 : $i, X18 : $i]:
% 0.21/0.48         (~ (m1_pre_topc @ X17 @ X18)
% 0.21/0.48          | (l1_pre_topc @ X17)
% 0.21/0.48          | ~ (l1_pre_topc @ X18))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.48  thf('12', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('14', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.48      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (((~ (l1_struct_0 @ sk_C) | (r1_tsep_1 @ sk_B_1 @ sk_C)))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_C @ sk_B_1)))),
% 0.21/0.48      inference('demod', [status(thm)], ['9', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (((~ (l1_pre_topc @ sk_C) | (r1_tsep_1 @ sk_B_1 @ sk_C)))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_C @ sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['3', '15'])).
% 0.21/0.48  thf('17', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X17 : $i, X18 : $i]:
% 0.21/0.48         (~ (m1_pre_topc @ X17 @ X18)
% 0.21/0.48          | (l1_pre_topc @ X17)
% 0.21/0.48          | ~ (l1_pre_topc @ X18))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.48  thf('19', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C))),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('21', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.48      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (((r1_tsep_1 @ sk_B_1 @ sk_C)) <= (((r1_tsep_1 @ sk_C @ sk_B_1)))),
% 0.21/0.48      inference('demod', [status(thm)], ['16', '21'])).
% 0.21/0.48  thf(d3_tsep_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( l1_struct_0 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( l1_struct_0 @ B ) =>
% 0.21/0.48           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.21/0.48             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (![X20 : $i, X21 : $i]:
% 0.21/0.48         (~ (l1_struct_0 @ X20)
% 0.21/0.48          | ~ (r1_tsep_1 @ X21 @ X20)
% 0.21/0.48          | (r1_xboole_0 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.21/0.48          | ~ (l1_struct_0 @ X21))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (((~ (l1_struct_0 @ sk_B_1)
% 0.21/0.48         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))
% 0.21/0.48         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_C @ sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (((~ (l1_pre_topc @ sk_B_1)
% 0.21/0.48         | ~ (l1_struct_0 @ sk_C)
% 0.21/0.48         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_C @ sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '24'])).
% 0.21/0.48  thf('26', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.48      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (((~ (l1_struct_0 @ sk_C)
% 0.21/0.48         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_C @ sk_B_1)))),
% 0.21/0.48      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (((~ (l1_pre_topc @ sk_C)
% 0.21/0.48         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_C @ sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '27'])).
% 0.21/0.48  thf('29', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.48      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (((r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_C @ sk_B_1)))),
% 0.21/0.48      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.48  thf('31', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('32', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t4_tsep_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.48               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) <=>
% 0.21/0.48                 ( m1_pre_topc @ B @ C ) ) ) ) ) ) ))).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.48         (~ (m1_pre_topc @ X24 @ X25)
% 0.21/0.48          | ~ (m1_pre_topc @ X24 @ X26)
% 0.21/0.48          | (r1_tarski @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X26))
% 0.21/0.48          | ~ (m1_pre_topc @ X26 @ X25)
% 0.21/0.48          | ~ (l1_pre_topc @ X25)
% 0.21/0.48          | ~ (v2_pre_topc @ X25))),
% 0.21/0.48      inference('cnf', [status(esa)], [t4_tsep_1])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (v2_pre_topc @ sk_A)
% 0.21/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.48          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.48          | (r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ X0))
% 0.21/0.48          | ~ (m1_pre_topc @ sk_B_1 @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.48  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.21/0.48          | (r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ X0))
% 0.21/0.48          | ~ (m1_pre_topc @ sk_B_1 @ X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      ((~ (m1_pre_topc @ sk_B_1 @ sk_C)
% 0.21/0.48        | (r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['31', '37'])).
% 0.21/0.48  thf('39', plain, ((m1_pre_topc @ sk_B_1 @ sk_C)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      ((r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))),
% 0.21/0.48      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.48  thf(t10_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.48         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ X6 @ (k2_xboole_0 @ X8 @ X7)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.21/0.48  thf('42', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (r1_tarski @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.48          (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.48  thf(t73_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.21/0.48       ( r1_tarski @ A @ B ) ))).
% 0.21/0.48  thf('43', plain,
% 0.21/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.48         ((r1_tarski @ X9 @ X10)
% 0.21/0.48          | ~ (r1_tarski @ X9 @ (k2_xboole_0 @ X10 @ X11))
% 0.21/0.48          | ~ (r1_xboole_0 @ X9 @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [t73_xboole_1])).
% 0.21/0.48  thf('44', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))
% 0.21/0.48          | (r1_tarski @ (u1_struct_0 @ sk_B_1) @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      ((![X0 : $i]: (r1_tarski @ (u1_struct_0 @ sk_B_1) @ X0))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_C @ sk_B_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['30', '44'])).
% 0.21/0.48  thf('46', plain,
% 0.21/0.48      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('47', plain,
% 0.21/0.48      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('48', plain,
% 0.21/0.48      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.48  thf('49', plain,
% 0.21/0.48      (((r1_tsep_1 @ sk_B_1 @ sk_C)) <= (((r1_tsep_1 @ sk_B_1 @ sk_C)))),
% 0.21/0.48      inference('split', [status(esa)], ['5'])).
% 0.21/0.48  thf('50', plain,
% 0.21/0.48      (![X20 : $i, X21 : $i]:
% 0.21/0.48         (~ (l1_struct_0 @ X20)
% 0.21/0.48          | ~ (r1_tsep_1 @ X21 @ X20)
% 0.21/0.48          | (r1_xboole_0 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.21/0.48          | ~ (l1_struct_0 @ X21))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.48  thf('51', plain,
% 0.21/0.48      (((~ (l1_struct_0 @ sk_B_1)
% 0.21/0.48         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))
% 0.21/0.48         | ~ (l1_struct_0 @ sk_C))) <= (((r1_tsep_1 @ sk_B_1 @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.48  thf('52', plain,
% 0.21/0.48      (((~ (l1_pre_topc @ sk_B_1)
% 0.21/0.48         | ~ (l1_struct_0 @ sk_C)
% 0.21/0.48         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_B_1 @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['48', '51'])).
% 0.21/0.48  thf('53', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.48      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf('54', plain,
% 0.21/0.48      (((~ (l1_struct_0 @ sk_C)
% 0.21/0.48         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_B_1 @ sk_C)))),
% 0.21/0.48      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.48  thf('55', plain,
% 0.21/0.48      (((~ (l1_pre_topc @ sk_C)
% 0.21/0.48         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_B_1 @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['47', '54'])).
% 0.21/0.48  thf('56', plain, ((l1_pre_topc @ sk_C)),
% 0.21/0.48      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('57', plain,
% 0.21/0.48      (((r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C)))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_B_1 @ sk_C)))),
% 0.21/0.48      inference('demod', [status(thm)], ['55', '56'])).
% 0.21/0.48  thf('58', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C))
% 0.21/0.48          | (r1_tarski @ (u1_struct_0 @ sk_B_1) @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.48  thf('59', plain,
% 0.21/0.48      ((![X0 : $i]: (r1_tarski @ (u1_struct_0 @ sk_B_1) @ X0))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_B_1 @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.48  thf(d1_xboole_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.48  thf('60', plain,
% 0.21/0.48      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.48  thf(t7_ordinal1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.48  thf('61', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X12 @ X13) | ~ (r1_tarski @ X13 @ X12))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.48  thf('62', plain,
% 0.21/0.48      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.48  thf('63', plain,
% 0.21/0.48      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_B_1 @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['59', '62'])).
% 0.21/0.48  thf(fc2_struct_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.48       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.48  thf('64', plain,
% 0.21/0.48      (![X19 : $i]:
% 0.21/0.48         (~ (v1_xboole_0 @ (u1_struct_0 @ X19))
% 0.21/0.48          | ~ (l1_struct_0 @ X19)
% 0.21/0.48          | (v2_struct_0 @ X19))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.48  thf('65', plain,
% 0.21/0.48      ((((v2_struct_0 @ sk_B_1) | ~ (l1_struct_0 @ sk_B_1)))
% 0.21/0.48         <= (((r1_tsep_1 @ sk_B_1 @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.48  thf('66', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('67', plain,
% 0.21/0.48      ((~ (l1_struct_0 @ sk_B_1)) <= (((r1_tsep_1 @ sk_B_1 @ sk_C)))),
% 0.21/0.48      inference('clc', [status(thm)], ['65', '66'])).
% 0.21/0.48  thf('68', plain,
% 0.21/0.48      ((~ (l1_pre_topc @ sk_B_1)) <= (((r1_tsep_1 @ sk_B_1 @ sk_C)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['46', '67'])).
% 0.21/0.48  thf('69', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.48      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf('70', plain, (~ ((r1_tsep_1 @ sk_B_1 @ sk_C))),
% 0.21/0.48      inference('demod', [status(thm)], ['68', '69'])).
% 0.21/0.48  thf('71', plain,
% 0.21/0.48      (((r1_tsep_1 @ sk_C @ sk_B_1)) | ((r1_tsep_1 @ sk_B_1 @ sk_C))),
% 0.21/0.48      inference('split', [status(esa)], ['5'])).
% 0.21/0.48  thf('72', plain, (((r1_tsep_1 @ sk_C @ sk_B_1))),
% 0.21/0.48      inference('sat_resolution*', [status(thm)], ['70', '71'])).
% 0.21/0.48  thf('73', plain, (![X0 : $i]: (r1_tarski @ (u1_struct_0 @ sk_B_1) @ X0)),
% 0.21/0.48      inference('simpl_trail', [status(thm)], ['45', '72'])).
% 0.21/0.48  thf('74', plain,
% 0.21/0.48      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.48  thf('75', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.48  thf('76', plain,
% 0.21/0.48      (![X19 : $i]:
% 0.21/0.48         (~ (v1_xboole_0 @ (u1_struct_0 @ X19))
% 0.21/0.48          | ~ (l1_struct_0 @ X19)
% 0.21/0.48          | (v2_struct_0 @ X19))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.48  thf('77', plain, (((v2_struct_0 @ sk_B_1) | ~ (l1_struct_0 @ sk_B_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['75', '76'])).
% 0.21/0.48  thf('78', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('79', plain, (~ (l1_struct_0 @ sk_B_1)),
% 0.21/0.48      inference('clc', [status(thm)], ['77', '78'])).
% 0.21/0.48  thf('80', plain, (~ (l1_pre_topc @ sk_B_1)),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '79'])).
% 0.21/0.48  thf('81', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.48      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf('82', plain, ($false), inference('demod', [status(thm)], ['80', '81'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
