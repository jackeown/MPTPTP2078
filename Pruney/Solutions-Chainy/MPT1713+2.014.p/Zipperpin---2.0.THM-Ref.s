%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QC3jHctsj2

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 243 expanded)
%              Number of leaves         :   30 (  82 expanded)
%              Depth                    :   19
%              Number of atoms          :  653 (2407 expanded)
%              Number of equality atoms :    5 (  10 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('1',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('2',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('3',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('4',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
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
    ( ( r1_tsep_1 @ sk_B_1 @ sk_C_1 )
    | ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_B_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['5'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_struct_0 @ X24 )
      | ~ ( l1_struct_0 @ X25 )
      | ( r1_tsep_1 @ X25 @ X24 )
      | ~ ( r1_tsep_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('8',plain,
    ( ( ( r1_tsep_1 @ sk_B_1 @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( l1_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
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
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','15'])).

thf('17',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( l1_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
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
    ( ( r1_tsep_1 @ sk_B_1 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['16','21'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('23',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_struct_0 @ X22 )
      | ~ ( r1_tsep_1 @ X23 @ X22 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('24',plain,
    ( ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('27',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['19','20'])).

thf('30',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_pre_topc @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('32',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['19','20'])).

thf('35',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('36',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('38',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('39',plain,
    ( ( k2_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('40',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('41',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X3 @ X6 )
      | ( r2_hidden @ X3 @ X5 )
      | ( X5
       != ( k2_xboole_0 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('42',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ ( k2_xboole_0 @ X6 @ X4 ) )
      | ~ ( r2_hidden @ X3 @ X6 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('45',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ~ ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['39','48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['30','49'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('51',plain,(
    ! [X21: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('52',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('54',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('55',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('56',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf('57',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_struct_0 @ X22 )
      | ~ ( r1_tsep_1 @ X23 @ X22 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('58',plain,
    ( ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('61',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['54','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['19','20'])).

thf('64',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['39','48'])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X21: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('68',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ~ ( l1_struct_0 @ sk_B_1 )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['53','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('73',plain,(
    ~ ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_B_1 )
    | ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf('75',plain,(
    r1_tsep_1 @ sk_C_1 @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['52','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['79','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QC3jHctsj2
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:59:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 105 iterations in 0.044s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(dt_l1_pre_topc, axiom,
% 0.21/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.50  thf('0', plain, (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.50  thf('1', plain, (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.50  thf('2', plain, (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.50  thf('3', plain, (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.50  thf('4', plain, (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.50  thf(t22_tmap_1, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.50               ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.50                 ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.50            ( l1_pre_topc @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.50              ( ![C:$i]:
% 0.21/0.50                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.50                  ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.50                    ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t22_tmap_1])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (((r1_tsep_1 @ sk_B_1 @ sk_C_1) | (r1_tsep_1 @ sk_C_1 @ sk_B_1))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (((r1_tsep_1 @ sk_C_1 @ sk_B_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.21/0.50      inference('split', [status(esa)], ['5'])).
% 0.21/0.50  thf(symmetry_r1_tsep_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.21/0.50       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X24 : $i, X25 : $i]:
% 0.21/0.50         (~ (l1_struct_0 @ X24)
% 0.21/0.50          | ~ (l1_struct_0 @ X25)
% 0.21/0.50          | (r1_tsep_1 @ X25 @ X24)
% 0.21/0.50          | ~ (r1_tsep_1 @ X24 @ X25))),
% 0.21/0.50      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      ((((r1_tsep_1 @ sk_B_1 @ sk_C_1)
% 0.21/0.50         | ~ (l1_struct_0 @ sk_B_1)
% 0.21/0.50         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (((~ (l1_pre_topc @ sk_B_1)
% 0.21/0.50         | ~ (l1_struct_0 @ sk_C_1)
% 0.21/0.50         | (r1_tsep_1 @ sk_B_1 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '8'])).
% 0.21/0.50  thf('10', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_m1_pre_topc, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X19 : $i, X20 : $i]:
% 0.21/0.50         (~ (m1_pre_topc @ X19 @ X20)
% 0.21/0.50          | (l1_pre_topc @ X19)
% 0.21/0.50          | ~ (l1_pre_topc @ X20))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.50  thf('12', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('14', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (((~ (l1_struct_0 @ sk_C_1) | (r1_tsep_1 @ sk_B_1 @ sk_C_1)))
% 0.21/0.50         <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.21/0.50      inference('demod', [status(thm)], ['9', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (((~ (l1_pre_topc @ sk_C_1) | (r1_tsep_1 @ sk_B_1 @ sk_C_1)))
% 0.21/0.50         <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '15'])).
% 0.21/0.50  thf('17', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X19 : $i, X20 : $i]:
% 0.21/0.50         (~ (m1_pre_topc @ X19 @ X20)
% 0.21/0.50          | (l1_pre_topc @ X19)
% 0.21/0.50          | ~ (l1_pre_topc @ X20))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.50  thf('19', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.50  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('21', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.50      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (((r1_tsep_1 @ sk_B_1 @ sk_C_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.21/0.50      inference('demod', [status(thm)], ['16', '21'])).
% 0.21/0.50  thf(d3_tsep_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_struct_0 @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( l1_struct_0 @ B ) =>
% 0.21/0.50           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.21/0.50             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X22 : $i, X23 : $i]:
% 0.21/0.50         (~ (l1_struct_0 @ X22)
% 0.21/0.50          | ~ (r1_tsep_1 @ X23 @ X22)
% 0.21/0.50          | (r1_xboole_0 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X22))
% 0.21/0.50          | ~ (l1_struct_0 @ X23))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (((~ (l1_struct_0 @ sk_B_1)
% 0.21/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.50         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (((~ (l1_pre_topc @ sk_B_1)
% 0.21/0.50         | ~ (l1_struct_0 @ sk_C_1)
% 0.21/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))))
% 0.21/0.50         <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '24'])).
% 0.21/0.50  thf('26', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (((~ (l1_struct_0 @ sk_C_1)
% 0.21/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))))
% 0.21/0.50         <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.21/0.50      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (((~ (l1_pre_topc @ sk_C_1)
% 0.21/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))))
% 0.21/0.50         <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '27'])).
% 0.21/0.50  thf('29', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.50      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.50         <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.21/0.50      inference('demod', [status(thm)], ['28', '29'])).
% 0.21/0.50  thf('31', plain, ((m1_pre_topc @ sk_B_1 @ sk_C_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t1_tsep_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_pre_topc @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.50           ( m1_subset_1 @
% 0.21/0.50             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X26 : $i, X27 : $i]:
% 0.21/0.50         (~ (m1_pre_topc @ X26 @ X27)
% 0.21/0.50          | (m1_subset_1 @ (u1_struct_0 @ X26) @ 
% 0.21/0.50             (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.21/0.50          | ~ (l1_pre_topc @ X27))),
% 0.21/0.50      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      ((~ (l1_pre_topc @ sk_C_1)
% 0.21/0.50        | (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.50           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.50  thf('34', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.50      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.50        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.50      inference('demod', [status(thm)], ['33', '34'])).
% 0.21/0.50  thf(t3_subset, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (![X15 : $i, X16 : $i]:
% 0.21/0.50         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      ((r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.50  thf(t12_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i]:
% 0.21/0.50         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (((k2_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.50         = (u1_struct_0 @ sk_C_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.50  thf(d1_xboole_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.50  thf(d3_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.21/0.50       ( ![D:$i]:
% 0.21/0.50         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.50           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X3 @ X6)
% 0.21/0.50          | (r2_hidden @ X3 @ X5)
% 0.21/0.50          | ((X5) != (k2_xboole_0 @ X6 @ X4)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.21/0.50         ((r2_hidden @ X3 @ (k2_xboole_0 @ X6 @ X4)) | ~ (r2_hidden @ X3 @ X6))),
% 0.21/0.50      inference('simplify', [status(thm)], ['41'])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ X0)
% 0.21/0.50          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X0 @ X1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['40', '42'])).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.50  thf(t3_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.50            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.50       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.50            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X11 @ X9)
% 0.21/0.50          | ~ (r2_hidden @ X11 @ X12)
% 0.21/0.50          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.21/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ X0)
% 0.21/0.50          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.21/0.50          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ X1)
% 0.21/0.50          | ~ (r1_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.21/0.50          | (v1_xboole_0 @ X1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['43', '46'])).
% 0.21/0.50  thf('48', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r1_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) | (v1_xboole_0 @ X1))),
% 0.21/0.50      inference('simplify', [status(thm)], ['47'])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      ((~ (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['39', '48'])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))
% 0.21/0.50         <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['30', '49'])).
% 0.21/0.50  thf(fc2_struct_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      (![X21 : $i]:
% 0.21/0.50         (~ (v1_xboole_0 @ (u1_struct_0 @ X21))
% 0.21/0.50          | ~ (l1_struct_0 @ X21)
% 0.21/0.50          | (v2_struct_0 @ X21))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      ((((v2_struct_0 @ sk_B_1) | ~ (l1_struct_0 @ sk_B_1)))
% 0.21/0.50         <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.50  thf('54', plain,
% 0.21/0.50      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.50  thf('55', plain,
% 0.21/0.50      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.50  thf('56', plain,
% 0.21/0.50      (((r1_tsep_1 @ sk_B_1 @ sk_C_1)) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.21/0.50      inference('split', [status(esa)], ['5'])).
% 0.21/0.50  thf('57', plain,
% 0.21/0.50      (![X22 : $i, X23 : $i]:
% 0.21/0.50         (~ (l1_struct_0 @ X22)
% 0.21/0.50          | ~ (r1_tsep_1 @ X23 @ X22)
% 0.21/0.50          | (r1_xboole_0 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X22))
% 0.21/0.50          | ~ (l1_struct_0 @ X23))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.50  thf('58', plain,
% 0.21/0.50      (((~ (l1_struct_0 @ sk_B_1)
% 0.21/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.50         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.50  thf('59', plain,
% 0.21/0.50      (((~ (l1_pre_topc @ sk_B_1)
% 0.21/0.50         | ~ (l1_struct_0 @ sk_C_1)
% 0.21/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))))
% 0.21/0.50         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['55', '58'])).
% 0.21/0.50  thf('60', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.50  thf('61', plain,
% 0.21/0.50      (((~ (l1_struct_0 @ sk_C_1)
% 0.21/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))))
% 0.21/0.50         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.21/0.50      inference('demod', [status(thm)], ['59', '60'])).
% 0.21/0.50  thf('62', plain,
% 0.21/0.50      (((~ (l1_pre_topc @ sk_C_1)
% 0.21/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))))
% 0.21/0.50         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['54', '61'])).
% 0.21/0.50  thf('63', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.50      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf('64', plain,
% 0.21/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.50         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.21/0.50      inference('demod', [status(thm)], ['62', '63'])).
% 0.21/0.50  thf('65', plain,
% 0.21/0.50      ((~ (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['39', '48'])).
% 0.21/0.50  thf('66', plain,
% 0.21/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))
% 0.21/0.50         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.50  thf('67', plain,
% 0.21/0.50      (![X21 : $i]:
% 0.21/0.50         (~ (v1_xboole_0 @ (u1_struct_0 @ X21))
% 0.21/0.50          | ~ (l1_struct_0 @ X21)
% 0.21/0.50          | (v2_struct_0 @ X21))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.50  thf('68', plain,
% 0.21/0.50      ((((v2_struct_0 @ sk_B_1) | ~ (l1_struct_0 @ sk_B_1)))
% 0.21/0.50         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.50  thf('69', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('70', plain,
% 0.21/0.50      ((~ (l1_struct_0 @ sk_B_1)) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.21/0.50      inference('clc', [status(thm)], ['68', '69'])).
% 0.21/0.50  thf('71', plain,
% 0.21/0.50      ((~ (l1_pre_topc @ sk_B_1)) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['53', '70'])).
% 0.21/0.50  thf('72', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.50  thf('73', plain, (~ ((r1_tsep_1 @ sk_B_1 @ sk_C_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['71', '72'])).
% 0.21/0.50  thf('74', plain,
% 0.21/0.50      (((r1_tsep_1 @ sk_C_1 @ sk_B_1)) | ((r1_tsep_1 @ sk_B_1 @ sk_C_1))),
% 0.21/0.50      inference('split', [status(esa)], ['5'])).
% 0.21/0.50  thf('75', plain, (((r1_tsep_1 @ sk_C_1 @ sk_B_1))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['73', '74'])).
% 0.21/0.50  thf('76', plain, (((v2_struct_0 @ sk_B_1) | ~ (l1_struct_0 @ sk_B_1))),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['52', '75'])).
% 0.21/0.50  thf('77', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('78', plain, (~ (l1_struct_0 @ sk_B_1)),
% 0.21/0.50      inference('clc', [status(thm)], ['76', '77'])).
% 0.21/0.50  thf('79', plain, (~ (l1_pre_topc @ sk_B_1)),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '78'])).
% 0.21/0.50  thf('80', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.50  thf('81', plain, ($false), inference('demod', [status(thm)], ['79', '80'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
