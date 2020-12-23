%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CxSEw6xSbV

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 227 expanded)
%              Number of leaves         :   27 (  76 expanded)
%              Depth                    :   26
%              Number of atoms          :  589 (2253 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('1',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('2',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('4',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
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
    ( ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( r1_tsep_1 @ sk_C_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_B )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_struct_0 @ X16 )
      | ~ ( l1_struct_0 @ X17 )
      | ( r1_tsep_1 @ X17 @ X16 )
      | ~ ( r1_tsep_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('8',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_tsep_1 @ sk_B @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_tsep_1 @ sk_B @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ( r1_tsep_1 @ sk_B @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','15'])).

thf('17',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( l1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['16','21'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( r1_tsep_1 @ X15 @ X14 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('24',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('26',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('27',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('28',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_struct_0 @ X14 )
      | ~ ( r1_tsep_1 @ X15 @ X14 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X15 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('30',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ~ ( l1_pre_topc @ sk_B )
      | ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['12','13'])).

thf('33',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['19','20'])).

thf('36',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('38',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('40',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['19','20'])).

thf('43',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('44',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('46',plain,(
    ! [X7: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('47',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('48',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X5 @ X4 )
      | ( r1_tarski @ X5 @ X3 )
      | ( X4
       != ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('49',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['38','50'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('52',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('53',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ~ ( l1_struct_0 @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( l1_pre_topc @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['25','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['12','13'])).

thf('58',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf('60',plain,(
    r1_tsep_1 @ sk_C_1 @ sk_B ),
    inference('sat_resolution*',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['24','60'])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_struct_0 @ sk_C_1 )
    | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['2','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['12','13'])).

thf('64',plain,
    ( ~ ( l1_struct_0 @ sk_C_1 )
    | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['19','20'])).

thf('67',plain,(
    r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('69',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('71',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X13: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ~ ( l1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['0','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['12','13'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['76','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CxSEw6xSbV
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 67 iterations in 0.029s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.48  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.21/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.48  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(dt_l1_pre_topc, axiom,
% 0.21/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.49  thf('0', plain, (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.49  thf('1', plain, (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.49  thf('2', plain, (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.49  thf('3', plain, (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.49  thf('4', plain, (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.49  thf(t22_tmap_1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.49               ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.49                 ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.49            ( l1_pre_topc @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.49              ( ![C:$i]:
% 0.21/0.49                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.49                  ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.49                    ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t22_tmap_1])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_B @ sk_C_1) | (r1_tsep_1 @ sk_C_1 @ sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_C_1 @ sk_B)) <= (((r1_tsep_1 @ sk_C_1 @ sk_B)))),
% 0.21/0.49      inference('split', [status(esa)], ['5'])).
% 0.21/0.49  thf(symmetry_r1_tsep_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.21/0.49       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X16 : $i, X17 : $i]:
% 0.21/0.49         (~ (l1_struct_0 @ X16)
% 0.21/0.49          | ~ (l1_struct_0 @ X17)
% 0.21/0.49          | (r1_tsep_1 @ X17 @ X16)
% 0.21/0.49          | ~ (r1_tsep_1 @ X16 @ X17))),
% 0.21/0.49      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      ((((r1_tsep_1 @ sk_B @ sk_C_1)
% 0.21/0.49         | ~ (l1_struct_0 @ sk_B)
% 0.21/0.49         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (((~ (l1_pre_topc @ sk_B)
% 0.21/0.49         | ~ (l1_struct_0 @ sk_C_1)
% 0.21/0.49         | (r1_tsep_1 @ sk_B @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '8'])).
% 0.21/0.49  thf('10', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_m1_pre_topc, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X11 @ X12)
% 0.21/0.49          | (l1_pre_topc @ X11)
% 0.21/0.49          | ~ (l1_pre_topc @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.49  thf('12', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.49  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('14', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (((~ (l1_struct_0 @ sk_C_1) | (r1_tsep_1 @ sk_B @ sk_C_1)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_C_1 @ sk_B)))),
% 0.21/0.49      inference('demod', [status(thm)], ['9', '14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (((~ (l1_pre_topc @ sk_C_1) | (r1_tsep_1 @ sk_B @ sk_C_1)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_C_1 @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '15'])).
% 0.21/0.49  thf('17', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X11 @ X12)
% 0.21/0.49          | (l1_pre_topc @ X11)
% 0.21/0.49          | ~ (l1_pre_topc @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.49  thf('19', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.49  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('21', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_B @ sk_C_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_B)))),
% 0.21/0.49      inference('demod', [status(thm)], ['16', '21'])).
% 0.21/0.49  thf(d3_tsep_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_struct_0 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( l1_struct_0 @ B ) =>
% 0.21/0.49           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.21/0.49             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X14 : $i, X15 : $i]:
% 0.21/0.49         (~ (l1_struct_0 @ X14)
% 0.21/0.49          | ~ (r1_tsep_1 @ X15 @ X14)
% 0.21/0.49          | (r1_xboole_0 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))
% 0.21/0.49          | ~ (l1_struct_0 @ X15))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (((~ (l1_struct_0 @ sk_B)
% 0.21/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.49         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_pre_topc @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_B @ sk_C_1)) <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.49      inference('split', [status(esa)], ['5'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (![X14 : $i, X15 : $i]:
% 0.21/0.49         (~ (l1_struct_0 @ X14)
% 0.21/0.49          | ~ (r1_tsep_1 @ X15 @ X14)
% 0.21/0.49          | (r1_xboole_0 @ (u1_struct_0 @ X15) @ (u1_struct_0 @ X14))
% 0.21/0.49          | ~ (l1_struct_0 @ X15))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (((~ (l1_struct_0 @ sk_B)
% 0.21/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.49         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (((~ (l1_pre_topc @ sk_B)
% 0.21/0.49         | ~ (l1_struct_0 @ sk_C_1)
% 0.21/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['27', '30'])).
% 0.21/0.49  thf('32', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (((~ (l1_struct_0 @ sk_C_1)
% 0.21/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (((~ (l1_pre_topc @ sk_C_1)
% 0.21/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['26', '33'])).
% 0.21/0.49  thf('35', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.49  thf(t69_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.49       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r1_xboole_0 @ X0 @ X1)
% 0.21/0.49          | ~ (r1_tarski @ X0 @ X1)
% 0.21/0.49          | (v1_xboole_0 @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      ((((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.49         | ~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.49  thf('39', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t1_tsep_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.49           ( m1_subset_1 @
% 0.21/0.49             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      (![X18 : $i, X19 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X18 @ X19)
% 0.21/0.49          | (m1_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.21/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.49          | ~ (l1_pre_topc @ X19))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_C_1)
% 0.21/0.49        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.49  thf('42', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.49  thf(t2_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.49       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i]:
% 0.21/0.49         ((r2_hidden @ X8 @ X9)
% 0.21/0.49          | (v1_xboole_0 @ X9)
% 0.21/0.49          | ~ (m1_subset_1 @ X8 @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.49        | (r2_hidden @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.49  thf(fc1_subset_1, axiom,
% 0.21/0.49    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.49  thf('46', plain, (![X7 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      ((r2_hidden @ (u1_struct_0 @ sk_B) @ 
% 0.21/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.49      inference('clc', [status(thm)], ['45', '46'])).
% 0.21/0.49  thf(d1_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X5 @ X4)
% 0.21/0.49          | (r1_tarski @ X5 @ X3)
% 0.21/0.49          | ((X4) != (k1_zfmisc_1 @ X3)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (![X3 : $i, X5 : $i]:
% 0.21/0.49         ((r1_tarski @ X5 @ X3) | ~ (r2_hidden @ X5 @ (k1_zfmisc_1 @ X3)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['48'])).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['47', '49'])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_B)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['38', '50'])).
% 0.21/0.49  thf(fc2_struct_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.49       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      (![X13 : $i]:
% 0.21/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X13))
% 0.21/0.49          | ~ (l1_struct_0 @ X13)
% 0.21/0.49          | (v2_struct_0 @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      ((((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.49  thf('54', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('55', plain,
% 0.21/0.49      ((~ (l1_struct_0 @ sk_B)) <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.49      inference('clc', [status(thm)], ['53', '54'])).
% 0.21/0.49  thf('56', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_B)) <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['25', '55'])).
% 0.21/0.49  thf('57', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('58', plain, (~ ((r1_tsep_1 @ sk_B @ sk_C_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['56', '57'])).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_C_1 @ sk_B)) | ((r1_tsep_1 @ sk_B @ sk_C_1))),
% 0.21/0.49      inference('split', [status(esa)], ['5'])).
% 0.21/0.49  thf('60', plain, (((r1_tsep_1 @ sk_C_1 @ sk_B))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['58', '59'])).
% 0.21/0.49  thf('61', plain,
% 0.21/0.49      ((~ (l1_struct_0 @ sk_B)
% 0.21/0.49        | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.49        | ~ (l1_struct_0 @ sk_C_1))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['24', '60'])).
% 0.21/0.49  thf('62', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_B)
% 0.21/0.49        | ~ (l1_struct_0 @ sk_C_1)
% 0.21/0.49        | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '61'])).
% 0.21/0.49  thf('63', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('64', plain,
% 0.21/0.49      ((~ (l1_struct_0 @ sk_C_1)
% 0.21/0.49        | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['62', '63'])).
% 0.21/0.49  thf('65', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_C_1)
% 0.21/0.49        | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '64'])).
% 0.21/0.49  thf('66', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('67', plain,
% 0.21/0.49      ((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['65', '66'])).
% 0.21/0.49  thf('68', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r1_xboole_0 @ X0 @ X1)
% 0.21/0.49          | ~ (r1_tarski @ X0 @ X1)
% 0.21/0.49          | (v1_xboole_0 @ X0))),
% 0.21/0.49      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.21/0.49  thf('69', plain,
% 0.21/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.21/0.49        | ~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.49  thf('70', plain,
% 0.21/0.49      ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['47', '49'])).
% 0.21/0.49  thf('71', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['69', '70'])).
% 0.21/0.49  thf('72', plain,
% 0.21/0.49      (![X13 : $i]:
% 0.21/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X13))
% 0.21/0.49          | ~ (l1_struct_0 @ X13)
% 0.21/0.49          | (v2_struct_0 @ X13))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.49  thf('73', plain, (((v2_struct_0 @ sk_B) | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.49  thf('74', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('75', plain, (~ (l1_struct_0 @ sk_B)),
% 0.21/0.49      inference('clc', [status(thm)], ['73', '74'])).
% 0.21/0.49  thf('76', plain, (~ (l1_pre_topc @ sk_B)),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '75'])).
% 0.21/0.49  thf('77', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.49  thf('78', plain, ($false), inference('demod', [status(thm)], ['76', '77'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
