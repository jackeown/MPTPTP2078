%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JNEZfCo1oM

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 804 expanded)
%              Number of leaves         :   27 ( 240 expanded)
%              Depth                    :   28
%              Number of atoms          :  881 (10859 expanded)
%              Number of equality atoms :    2 (  12 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('1',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('2',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('4',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('5',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('6',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('7',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf(t24_tmap_1,conjecture,(
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
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ A ) )
                 => ( ( m1_pre_topc @ B @ C )
                   => ( ( ~ ( r1_tsep_1 @ C @ D )
                        & ~ ( r1_tsep_1 @ D @ C ) )
                      | ( ( r1_tsep_1 @ B @ D )
                        & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) )).

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
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ A ) )
                   => ( ( m1_pre_topc @ B @ C )
                     => ( ( ~ ( r1_tsep_1 @ C @ D )
                          & ~ ( r1_tsep_1 @ D @ C ) )
                        | ( ( r1_tsep_1 @ B @ D )
                          & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_tmap_1])).

thf('8',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(split,[status(esa)],['8'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( r1_tsep_1 @ X17 @ X16 )
      | ~ ( r1_tsep_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('11',plain,
    ( ( ( r1_tsep_1 @ sk_C_1 @ sk_D )
      | ~ ( l1_struct_0 @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_C_1 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('15',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_C_1 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_C_1 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','18'])).

thf('20',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['19','24'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('26',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( r1_tsep_1 @ X15 @ X14 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('27',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('30',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['22','23'])).

thf('33',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('35',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('38',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('39',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('41',plain,(
    ! [X8: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('42',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('43',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r1_tarski @ X6 @ X4 )
      | ( X5
       != ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('44',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X2 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','47'])).

thf('49',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ( r1_tsep_1 @ X15 @ X14 )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('50',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','50'])).

thf('52',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X12 @ X13 )
      | ( l1_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('54',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['51','56'])).

thf('58',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['22','23'])).

thf('60',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( r1_tsep_1 @ X17 @ X16 )
      | ~ ( r1_tsep_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('62',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('64',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('65',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('66',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('67',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('68',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('69',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['8'])).

thf('70',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( r1_tsep_1 @ X15 @ X14 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('71',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('74',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['67','74'])).

thf('76',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['22','23'])).

thf('77',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ X0 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('79',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ( r1_tsep_1 @ X15 @ X14 )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('81',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D )
      | ~ ( l1_struct_0 @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['66','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['54','55'])).

thf('84',plain,
    ( ( ~ ( l1_struct_0 @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ( r1_tsep_1 @ sk_B @ sk_D ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['65','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['22','23'])).

thf('87',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( r1_tsep_1 @ X17 @ X16 )
      | ~ ( r1_tsep_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('89',plain,
    ( ( ( r1_tsep_1 @ sk_D @ sk_B )
      | ~ ( l1_struct_0 @ sk_D )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['64','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['22','23'])).

thf('92',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ( r1_tsep_1 @ sk_D @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['63','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['54','55'])).

thf('95',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['96'])).

thf('98',plain,
    ( ~ ( r1_tsep_1 @ sk_C_1 @ sk_D )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['95','97'])).

thf('99',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('100',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['96'])).

thf('101',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['96'])).

thf('103',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_C_1 )
    | ( r1_tsep_1 @ sk_C_1 @ sk_D ) ),
    inference(split,[status(esa)],['8'])).

thf('104',plain,(
    r1_tsep_1 @ sk_D @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['98','101','102','103'])).

thf('105',plain,
    ( ( r1_tsep_1 @ sk_D @ sk_B )
    | ~ ( l1_struct_0 @ sk_D )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['62','104'])).

thf('106',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ~ ( l1_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['1','105'])).

thf('107',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['22','23'])).

thf('108',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ~ ( r1_tsep_1 @ sk_D @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['96'])).

thf('110',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
   <= ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('111',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['96'])).

thf('112',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D )
    | ~ ( r1_tsep_1 @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['98','101','103','112','102'])).

thf('114',plain,(
    ~ ( r1_tsep_1 @ sk_D @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['109','113'])).

thf('115',plain,(
    ~ ( l1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['108','114'])).

thf('116',plain,(
    ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['0','115'])).

thf('117',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['54','55'])).

thf('118',plain,(
    $false ),
    inference(demod,[status(thm)],['116','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JNEZfCo1oM
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:34:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 98 iterations in 0.048s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.51  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.51  thf(dt_l1_pre_topc, axiom,
% 0.20/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.51  thf('0', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.51  thf('1', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.51  thf('2', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.51  thf('3', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.51  thf('4', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.51  thf('5', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.51  thf('6', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.51  thf('7', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.51  thf(t24_tmap_1, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.51               ( ![D:$i]:
% 0.20/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.51                   ( ( m1_pre_topc @ B @ C ) =>
% 0.20/0.51                     ( ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.20/0.51                         ( ~( r1_tsep_1 @ D @ C ) ) ) | 
% 0.20/0.51                       ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.51            ( l1_pre_topc @ A ) ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.51              ( ![C:$i]:
% 0.20/0.51                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.51                  ( ![D:$i]:
% 0.20/0.51                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.51                      ( ( m1_pre_topc @ B @ C ) =>
% 0.20/0.51                        ( ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.20/0.51                            ( ~( r1_tsep_1 @ D @ C ) ) ) | 
% 0.20/0.51                          ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t24_tmap_1])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (((r1_tsep_1 @ sk_C_1 @ sk_D) | (r1_tsep_1 @ sk_D @ sk_C_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (((r1_tsep_1 @ sk_D @ sk_C_1)) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['8'])).
% 0.20/0.51  thf(symmetry_r1_tsep_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.20/0.51       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i]:
% 0.20/0.51         (~ (l1_struct_0 @ X16)
% 0.20/0.51          | ~ (l1_struct_0 @ X17)
% 0.20/0.51          | (r1_tsep_1 @ X17 @ X16)
% 0.20/0.51          | ~ (r1_tsep_1 @ X16 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      ((((r1_tsep_1 @ sk_C_1 @ sk_D)
% 0.20/0.51         | ~ (l1_struct_0 @ sk_C_1)
% 0.20/0.51         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (((~ (l1_pre_topc @ sk_C_1)
% 0.20/0.51         | ~ (l1_struct_0 @ sk_D)
% 0.20/0.51         | (r1_tsep_1 @ sk_C_1 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '11'])).
% 0.20/0.51  thf('13', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_m1_pre_topc, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]:
% 0.20/0.51         (~ (m1_pre_topc @ X12 @ X13)
% 0.20/0.51          | (l1_pre_topc @ X12)
% 0.20/0.51          | ~ (l1_pre_topc @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.51  thf('15', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.51  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('17', plain, ((l1_pre_topc @ sk_C_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_C_1 @ sk_D)))
% 0.20/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['12', '17'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_C_1 @ sk_D)))
% 0.20/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '18'])).
% 0.20/0.51  thf('20', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]:
% 0.20/0.51         (~ (m1_pre_topc @ X12 @ X13)
% 0.20/0.51          | (l1_pre_topc @ X12)
% 0.20/0.51          | ~ (l1_pre_topc @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.51  thf('22', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.51  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('24', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (((r1_tsep_1 @ sk_C_1 @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['19', '24'])).
% 0.20/0.51  thf(d3_tsep_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_struct_0 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( l1_struct_0 @ B ) =>
% 0.20/0.51           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.20/0.51             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i]:
% 0.20/0.51         (~ (l1_struct_0 @ X14)
% 0.20/0.51          | ~ (r1_tsep_1 @ X15 @ X14)
% 0.20/0.51          | (r1_xboole_0 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))
% 0.20/0.51          | ~ (l1_struct_0 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (((~ (l1_struct_0 @ sk_C_1)
% 0.20/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))
% 0.20/0.51         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (((~ (l1_pre_topc @ sk_C_1)
% 0.20/0.51         | ~ (l1_struct_0 @ sk_D)
% 0.20/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))))
% 0.20/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '27'])).
% 0.20/0.51  thf('29', plain, ((l1_pre_topc @ sk_C_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (((~ (l1_struct_0 @ sk_D)
% 0.20/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))))
% 0.20/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (((~ (l1_pre_topc @ sk_D)
% 0.20/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))))
% 0.20/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '30'])).
% 0.20/0.51  thf('32', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D)))
% 0.20/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf('34', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t1_tsep_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_pre_topc @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.51           ( m1_subset_1 @
% 0.20/0.51             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (![X18 : $i, X19 : $i]:
% 0.20/0.51         (~ (m1_pre_topc @ X18 @ X19)
% 0.20/0.51          | (m1_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.20/0.51             (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.20/0.51          | ~ (l1_pre_topc @ X19))),
% 0.20/0.51      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      ((~ (l1_pre_topc @ sk_C_1)
% 0.20/0.51        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.51  thf('37', plain, ((l1_pre_topc @ sk_C_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['36', '37'])).
% 0.20/0.51  thf(t2_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.51       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i]:
% 0.20/0.51         ((r2_hidden @ X9 @ X10)
% 0.20/0.51          | (v1_xboole_0 @ X10)
% 0.20/0.51          | ~ (m1_subset_1 @ X9 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.20/0.51        | (r2_hidden @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.51  thf(fc1_subset_1, axiom,
% 0.20/0.51    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.51  thf('41', plain, (![X8 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      ((r2_hidden @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.51        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.51      inference('clc', [status(thm)], ['40', '41'])).
% 0.20/0.51  thf(d1_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X6 @ X5)
% 0.20/0.51          | (r1_tarski @ X6 @ X4)
% 0.20/0.51          | ((X5) != (k1_zfmisc_1 @ X4)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      (![X4 : $i, X6 : $i]:
% 0.20/0.51         ((r1_tarski @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['43'])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['42', '44'])).
% 0.20/0.51  thf(t63_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.20/0.51       ( r1_xboole_0 @ A @ C ) ))).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (r1_tarski @ X0 @ X1)
% 0.20/0.51          | ~ (r1_xboole_0 @ X1 @ X2)
% 0.20/0.51          | (r1_xboole_0 @ X0 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ X0)
% 0.20/0.51          | ~ (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.20/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['33', '47'])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i]:
% 0.20/0.51         (~ (l1_struct_0 @ X14)
% 0.20/0.51          | ~ (r1_xboole_0 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))
% 0.20/0.51          | (r1_tsep_1 @ X15 @ X14)
% 0.20/0.51          | ~ (l1_struct_0 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      (((~ (l1_struct_0 @ sk_B)
% 0.20/0.51         | (r1_tsep_1 @ sk_B @ sk_D)
% 0.20/0.51         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      (((~ (l1_pre_topc @ sk_B)
% 0.20/0.51         | ~ (l1_struct_0 @ sk_D)
% 0.20/0.51         | (r1_tsep_1 @ sk_B @ sk_D))) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '50'])).
% 0.20/0.51  thf('52', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i]:
% 0.20/0.51         (~ (m1_pre_topc @ X12 @ X13)
% 0.20/0.51          | (l1_pre_topc @ X12)
% 0.20/0.51          | ~ (l1_pre_topc @ X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.51  thf('54', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.51  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('56', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('demod', [status(thm)], ['54', '55'])).
% 0.20/0.51  thf('57', plain,
% 0.20/0.51      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.20/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['51', '56'])).
% 0.20/0.51  thf('58', plain,
% 0.20/0.51      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.20/0.51         <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '57'])).
% 0.20/0.51  thf('59', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.51  thf('60', plain,
% 0.20/0.51      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['58', '59'])).
% 0.20/0.51  thf('61', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i]:
% 0.20/0.51         (~ (l1_struct_0 @ X16)
% 0.20/0.51          | ~ (l1_struct_0 @ X17)
% 0.20/0.51          | (r1_tsep_1 @ X17 @ X16)
% 0.20/0.51          | ~ (r1_tsep_1 @ X16 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.20/0.51  thf('62', plain,
% 0.20/0.51      ((((r1_tsep_1 @ sk_D @ sk_B)
% 0.20/0.51         | ~ (l1_struct_0 @ sk_D)
% 0.20/0.51         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.51  thf('63', plain,
% 0.20/0.51      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.51  thf('64', plain,
% 0.20/0.51      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.51  thf('65', plain,
% 0.20/0.51      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.51  thf('66', plain,
% 0.20/0.51      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.51  thf('67', plain,
% 0.20/0.51      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.51  thf('68', plain,
% 0.20/0.51      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_pre_topc @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.51  thf('69', plain,
% 0.20/0.51      (((r1_tsep_1 @ sk_C_1 @ sk_D)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.20/0.51      inference('split', [status(esa)], ['8'])).
% 0.20/0.51  thf('70', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i]:
% 0.20/0.51         (~ (l1_struct_0 @ X14)
% 0.20/0.51          | ~ (r1_tsep_1 @ X15 @ X14)
% 0.20/0.51          | (r1_xboole_0 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))
% 0.20/0.51          | ~ (l1_struct_0 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.51  thf('71', plain,
% 0.20/0.51      (((~ (l1_struct_0 @ sk_C_1)
% 0.20/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))
% 0.20/0.51         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.51  thf('72', plain,
% 0.20/0.51      (((~ (l1_pre_topc @ sk_C_1)
% 0.20/0.51         | ~ (l1_struct_0 @ sk_D)
% 0.20/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))))
% 0.20/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['68', '71'])).
% 0.20/0.51  thf('73', plain, ((l1_pre_topc @ sk_C_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.51  thf('74', plain,
% 0.20/0.51      (((~ (l1_struct_0 @ sk_D)
% 0.20/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))))
% 0.20/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.20/0.51      inference('demod', [status(thm)], ['72', '73'])).
% 0.20/0.51  thf('75', plain,
% 0.20/0.51      (((~ (l1_pre_topc @ sk_D)
% 0.20/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D))))
% 0.20/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['67', '74'])).
% 0.20/0.51  thf('76', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.51  thf('77', plain,
% 0.20/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ (u1_struct_0 @ sk_D)))
% 0.20/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.20/0.51      inference('demod', [status(thm)], ['75', '76'])).
% 0.20/0.51  thf('78', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ X0)
% 0.20/0.51          | ~ (r1_xboole_0 @ (u1_struct_0 @ sk_C_1) @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.51  thf('79', plain,
% 0.20/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D)))
% 0.20/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['77', '78'])).
% 0.20/0.51  thf('80', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i]:
% 0.20/0.51         (~ (l1_struct_0 @ X14)
% 0.20/0.51          | ~ (r1_xboole_0 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))
% 0.20/0.51          | (r1_tsep_1 @ X15 @ X14)
% 0.20/0.51          | ~ (l1_struct_0 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.51  thf('81', plain,
% 0.20/0.51      (((~ (l1_struct_0 @ sk_B)
% 0.20/0.51         | (r1_tsep_1 @ sk_B @ sk_D)
% 0.20/0.51         | ~ (l1_struct_0 @ sk_D))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['79', '80'])).
% 0.20/0.51  thf('82', plain,
% 0.20/0.51      (((~ (l1_pre_topc @ sk_B)
% 0.20/0.51         | ~ (l1_struct_0 @ sk_D)
% 0.20/0.51         | (r1_tsep_1 @ sk_B @ sk_D))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['66', '81'])).
% 0.20/0.51  thf('83', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('demod', [status(thm)], ['54', '55'])).
% 0.20/0.51  thf('84', plain,
% 0.20/0.51      (((~ (l1_struct_0 @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.20/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.20/0.51      inference('demod', [status(thm)], ['82', '83'])).
% 0.20/0.51  thf('85', plain,
% 0.20/0.51      (((~ (l1_pre_topc @ sk_D) | (r1_tsep_1 @ sk_B @ sk_D)))
% 0.20/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['65', '84'])).
% 0.20/0.51  thf('86', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.51  thf('87', plain,
% 0.20/0.51      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.20/0.51      inference('demod', [status(thm)], ['85', '86'])).
% 0.20/0.51  thf('88', plain,
% 0.20/0.51      (![X16 : $i, X17 : $i]:
% 0.20/0.51         (~ (l1_struct_0 @ X16)
% 0.20/0.51          | ~ (l1_struct_0 @ X17)
% 0.20/0.51          | (r1_tsep_1 @ X17 @ X16)
% 0.20/0.51          | ~ (r1_tsep_1 @ X16 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.20/0.51  thf('89', plain,
% 0.20/0.51      ((((r1_tsep_1 @ sk_D @ sk_B)
% 0.20/0.51         | ~ (l1_struct_0 @ sk_D)
% 0.20/0.51         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['87', '88'])).
% 0.20/0.51  thf('90', plain,
% 0.20/0.51      (((~ (l1_pre_topc @ sk_D)
% 0.20/0.51         | ~ (l1_struct_0 @ sk_B)
% 0.20/0.51         | (r1_tsep_1 @ sk_D @ sk_B))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['64', '89'])).
% 0.20/0.51  thf('91', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.51  thf('92', plain,
% 0.20/0.51      (((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.20/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.20/0.51      inference('demod', [status(thm)], ['90', '91'])).
% 0.20/0.51  thf('93', plain,
% 0.20/0.51      (((~ (l1_pre_topc @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B)))
% 0.20/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['63', '92'])).
% 0.20/0.51  thf('94', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('demod', [status(thm)], ['54', '55'])).
% 0.20/0.51  thf('95', plain,
% 0.20/0.51      (((r1_tsep_1 @ sk_D @ sk_B)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.20/0.51      inference('demod', [status(thm)], ['93', '94'])).
% 0.20/0.51  thf('96', plain,
% 0.20/0.51      ((~ (r1_tsep_1 @ sk_B @ sk_D) | ~ (r1_tsep_1 @ sk_D @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('97', plain,
% 0.20/0.51      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['96'])).
% 0.20/0.51  thf('98', plain,
% 0.20/0.51      (~ ((r1_tsep_1 @ sk_C_1 @ sk_D)) | ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['95', '97'])).
% 0.20/0.51  thf('99', plain,
% 0.20/0.51      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D)))),
% 0.20/0.51      inference('demod', [status(thm)], ['85', '86'])).
% 0.20/0.51  thf('100', plain,
% 0.20/0.51      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.20/0.51      inference('split', [status(esa)], ['96'])).
% 0.20/0.51  thf('101', plain,
% 0.20/0.51      (((r1_tsep_1 @ sk_B @ sk_D)) | ~ ((r1_tsep_1 @ sk_C_1 @ sk_D))),
% 0.20/0.51      inference('sup-', [status(thm)], ['99', '100'])).
% 0.20/0.51  thf('102', plain,
% 0.20/0.51      (~ ((r1_tsep_1 @ sk_D @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D))),
% 0.20/0.51      inference('split', [status(esa)], ['96'])).
% 0.20/0.51  thf('103', plain,
% 0.20/0.51      (((r1_tsep_1 @ sk_D @ sk_C_1)) | ((r1_tsep_1 @ sk_C_1 @ sk_D))),
% 0.20/0.51      inference('split', [status(esa)], ['8'])).
% 0.20/0.51  thf('104', plain, (((r1_tsep_1 @ sk_D @ sk_C_1))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['98', '101', '102', '103'])).
% 0.20/0.51  thf('105', plain,
% 0.20/0.51      (((r1_tsep_1 @ sk_D @ sk_B)
% 0.20/0.51        | ~ (l1_struct_0 @ sk_D)
% 0.20/0.51        | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['62', '104'])).
% 0.20/0.51  thf('106', plain,
% 0.20/0.51      ((~ (l1_pre_topc @ sk_D)
% 0.20/0.51        | ~ (l1_struct_0 @ sk_B)
% 0.20/0.51        | (r1_tsep_1 @ sk_D @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '105'])).
% 0.20/0.51  thf('107', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.51  thf('108', plain, ((~ (l1_struct_0 @ sk_B) | (r1_tsep_1 @ sk_D @ sk_B))),
% 0.20/0.51      inference('demod', [status(thm)], ['106', '107'])).
% 0.20/0.51  thf('109', plain,
% 0.20/0.51      ((~ (r1_tsep_1 @ sk_D @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['96'])).
% 0.20/0.51  thf('110', plain,
% 0.20/0.51      (((r1_tsep_1 @ sk_B @ sk_D)) <= (((r1_tsep_1 @ sk_D @ sk_C_1)))),
% 0.20/0.51      inference('demod', [status(thm)], ['58', '59'])).
% 0.20/0.51  thf('111', plain,
% 0.20/0.51      ((~ (r1_tsep_1 @ sk_B @ sk_D)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D)))),
% 0.20/0.51      inference('split', [status(esa)], ['96'])).
% 0.20/0.51  thf('112', plain,
% 0.20/0.51      (((r1_tsep_1 @ sk_B @ sk_D)) | ~ ((r1_tsep_1 @ sk_D @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['110', '111'])).
% 0.20/0.51  thf('113', plain, (~ ((r1_tsep_1 @ sk_D @ sk_B))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)],
% 0.20/0.51                ['98', '101', '103', '112', '102'])).
% 0.20/0.51  thf('114', plain, (~ (r1_tsep_1 @ sk_D @ sk_B)),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['109', '113'])).
% 0.20/0.51  thf('115', plain, (~ (l1_struct_0 @ sk_B)),
% 0.20/0.51      inference('clc', [status(thm)], ['108', '114'])).
% 0.20/0.51  thf('116', plain, (~ (l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '115'])).
% 0.20/0.51  thf('117', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.51      inference('demod', [status(thm)], ['54', '55'])).
% 0.20/0.51  thf('118', plain, ($false), inference('demod', [status(thm)], ['116', '117'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
