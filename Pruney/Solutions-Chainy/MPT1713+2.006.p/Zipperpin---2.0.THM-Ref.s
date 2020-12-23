%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eyDynqdskn

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:15 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 315 expanded)
%              Number of leaves         :   36 ( 106 expanded)
%              Depth                    :   23
%              Number of atoms          :  837 (2831 expanded)
%              Number of equality atoms :   20 (  41 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X34: $i] :
      ( ( l1_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
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

thf('1',plain,(
    m1_pre_topc @ sk_B_1 @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( m1_pre_topc @ X42 @ X43 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X42 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X43 ) ) )
      | ~ ( l1_pre_topc @ X43 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_C_4 )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_4 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_pre_topc @ sk_C_4 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('5',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_pre_topc @ X35 @ X36 )
      | ( l1_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    l1_pre_topc @ sk_C_4 ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_4 ) ) ),
    inference(demod,[status(thm)],['3','8'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r2_hidden @ X32 @ X33 )
      | ( v1_xboole_0 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_4 ) ) )
    | ( r2_hidden @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_4 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ( X17 != X18 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X18: $i] :
      ( r1_tarski @ X18 @ X18 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('14',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ( r2_hidden @ X24 @ X26 )
      | ( X26
       != ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('15',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r2_hidden @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r2_hidden @ ( u1_struct_0 @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_4 ) ) ),
    inference(clc,[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X27 @ X26 )
      | ( r1_tarski @ X27 @ X25 )
      | ( X26
       != ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('21',plain,(
    ! [X25: $i,X27: $i] :
      ( ( r1_tarski @ X27 @ X25 )
      | ~ ( r2_hidden @ X27 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('23',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('24',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_4 ) )
    = ( u1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X34: $i] :
      ( ( l1_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('26',plain,(
    ! [X34: $i] :
      ( ( l1_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('27',plain,(
    ! [X34: $i] :
      ( ( l1_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('28',plain,(
    ! [X34: $i] :
      ( ( l1_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('29',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_C_4 )
    | ( r1_tsep_1 @ sk_C_4 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( r1_tsep_1 @ sk_C_4 @ sk_B_1 )
   <= ( r1_tsep_1 @ sk_C_4 @ sk_B_1 ) ),
    inference(split,[status(esa)],['29'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( l1_struct_0 @ X40 )
      | ~ ( l1_struct_0 @ X41 )
      | ( r1_tsep_1 @ X41 @ X40 )
      | ~ ( r1_tsep_1 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('32',plain,
    ( ( ( r1_tsep_1 @ sk_B_1 @ sk_C_4 )
      | ~ ( l1_struct_0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_C_4 ) )
   <= ( r1_tsep_1 @ sk_C_4 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_C_4 )
      | ( r1_tsep_1 @ sk_B_1 @ sk_C_4 ) )
   <= ( r1_tsep_1 @ sk_C_4 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_pre_topc @ X35 @ X36 )
      | ( l1_pre_topc @ X35 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_4 )
      | ( r1_tsep_1 @ sk_B_1 @ sk_C_4 ) )
   <= ( r1_tsep_1 @ sk_C_4 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('40',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_4 )
      | ( r1_tsep_1 @ sk_B_1 @ sk_C_4 ) )
   <= ( r1_tsep_1 @ sk_C_4 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_C_4 ),
    inference(demod,[status(thm)],['6','7'])).

thf('42',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_C_4 )
   <= ( r1_tsep_1 @ sk_C_4 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('43',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( l1_struct_0 @ X38 )
      | ~ ( r1_tsep_1 @ X39 @ X38 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( l1_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('44',plain,
    ( ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_4 ) )
      | ~ ( l1_struct_0 @ sk_C_4 ) )
   <= ( r1_tsep_1 @ sk_C_4 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_C_4 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_4 ) ) )
   <= ( r1_tsep_1 @ sk_C_4 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['36','37'])).

thf('47',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_4 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_4 ) ) )
   <= ( r1_tsep_1 @ sk_C_4 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_4 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_4 ) ) )
   <= ( r1_tsep_1 @ sk_C_4 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_C_4 ),
    inference(demod,[status(thm)],['6','7'])).

thf('50',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_4 ) )
   <= ( r1_tsep_1 @ sk_C_4 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('52',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k3_xboole_0 @ X13 @ X16 ) )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_4 ) ) )
   <= ( r1_tsep_1 @ sk_C_4 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('55',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('58',plain,(
    ! [X22: $i] :
      ( r1_tarski @ k1_xboole_0 @ X22 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('59',plain,(
    ! [X17: $i,X19: $i] :
      ( ( X17 = X19 )
      | ~ ( r1_tarski @ X19 @ X17 )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,
    ( ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_4 ) )
      = k1_xboole_0 )
   <= ( r1_tsep_1 @ sk_C_4 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['54','61'])).

thf('63',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( r1_tsep_1 @ sk_C_4 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['24','62'])).

thf('64',plain,(
    ! [X34: $i] :
      ( ( l1_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('65',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_4 ) )
    = ( u1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('66',plain,(
    ! [X34: $i] :
      ( ( l1_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('67',plain,(
    ! [X34: $i] :
      ( ( l1_struct_0 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('68',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_C_4 )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_4 ) ),
    inference(split,[status(esa)],['29'])).

thf('69',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( l1_struct_0 @ X38 )
      | ~ ( r1_tsep_1 @ X39 @ X38 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X39 ) @ ( u1_struct_0 @ X38 ) )
      | ~ ( l1_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('70',plain,
    ( ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_4 ) )
      | ~ ( l1_struct_0 @ sk_C_4 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ~ ( l1_pre_topc @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_C_4 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_4 ) ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['36','37'])).

thf('73',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_4 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_4 ) ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_4 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ~ ( l1_pre_topc @ sk_C_4 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_4 ) ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['66','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_C_4 ),
    inference(demod,[status(thm)],['6','7'])).

thf('76',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_4 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_4 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('78',plain,
    ( ( v1_xboole_0 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_4 ) ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('80',plain,
    ( ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_4 ) )
      = k1_xboole_0 )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( u1_struct_0 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_4 ) ),
    inference('sup+',[status(thm)],['65','80'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('82',plain,(
    ! [X37: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('83',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('84',plain,(
    ! [X23: $i] :
      ( r1_xboole_0 @ X23 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('85',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('86',plain,(
    ! [X18: $i] :
      ( r1_tarski @ X18 @ X18 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('87',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k3_xboole_0 @ X13 @ X16 ) )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('92',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['84','91'])).

thf('93',plain,
    ( ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_4 ) ),
    inference(demod,[status(thm)],['83','92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ~ ( l1_struct_0 @ sk_B_1 )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_4 ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( l1_pre_topc @ sk_B_1 )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['64','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['36','37'])).

thf('98',plain,(
    ~ ( r1_tsep_1 @ sk_B_1 @ sk_C_4 ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( r1_tsep_1 @ sk_C_4 @ sk_B_1 )
    | ( r1_tsep_1 @ sk_B_1 @ sk_C_4 ) ),
    inference(split,[status(esa)],['29'])).

thf('100',plain,(
    r1_tsep_1 @ sk_C_4 @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( u1_struct_0 @ sk_B_1 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['63','100'])).

thf('102',plain,(
    ! [X37: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('103',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['84','91'])).

thf('105',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['105','106'])).

thf('108',plain,(
    ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['36','37'])).

thf('110',plain,(
    $false ),
    inference(demod,[status(thm)],['108','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eyDynqdskn
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:57:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.68  % Solved by: fo/fo7.sh
% 0.46/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.68  % done 533 iterations in 0.222s
% 0.46/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.68  % SZS output start Refutation
% 0.46/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.68  thf(sk_C_4_type, type, sk_C_4: $i).
% 0.46/0.68  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.46/0.68  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.46/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.68  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.46/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.68  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.68  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.68  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.68  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.68  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.68  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.68  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.68  thf(dt_l1_pre_topc, axiom,
% 0.46/0.68    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.46/0.68  thf('0', plain, (![X34 : $i]: ((l1_struct_0 @ X34) | ~ (l1_pre_topc @ X34))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.68  thf(t22_tmap_1, conjecture,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.46/0.68           ( ![C:$i]:
% 0.46/0.68             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.46/0.68               ( ( m1_pre_topc @ B @ C ) =>
% 0.46/0.68                 ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.46/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.68    (~( ![A:$i]:
% 0.46/0.68        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.46/0.68            ( l1_pre_topc @ A ) ) =>
% 0.46/0.68          ( ![B:$i]:
% 0.46/0.68            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.46/0.68              ( ![C:$i]:
% 0.46/0.68                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.46/0.68                  ( ( m1_pre_topc @ B @ C ) =>
% 0.46/0.68                    ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ) )),
% 0.46/0.68    inference('cnf.neg', [status(esa)], [t22_tmap_1])).
% 0.46/0.68  thf('1', plain, ((m1_pre_topc @ sk_B_1 @ sk_C_4)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(t1_tsep_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( l1_pre_topc @ A ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( m1_pre_topc @ B @ A ) =>
% 0.46/0.68           ( m1_subset_1 @
% 0.46/0.68             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.46/0.68  thf('2', plain,
% 0.46/0.68      (![X42 : $i, X43 : $i]:
% 0.46/0.68         (~ (m1_pre_topc @ X42 @ X43)
% 0.46/0.68          | (m1_subset_1 @ (u1_struct_0 @ X42) @ 
% 0.46/0.68             (k1_zfmisc_1 @ (u1_struct_0 @ X43)))
% 0.46/0.68          | ~ (l1_pre_topc @ X43))),
% 0.46/0.68      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.46/0.68  thf('3', plain,
% 0.46/0.68      ((~ (l1_pre_topc @ sk_C_4)
% 0.46/0.68        | (m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.46/0.68           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_4))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.68  thf('4', plain, ((m1_pre_topc @ sk_C_4 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(dt_m1_pre_topc, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( l1_pre_topc @ A ) =>
% 0.46/0.68       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.46/0.68  thf('5', plain,
% 0.46/0.68      (![X35 : $i, X36 : $i]:
% 0.46/0.68         (~ (m1_pre_topc @ X35 @ X36)
% 0.46/0.68          | (l1_pre_topc @ X35)
% 0.46/0.68          | ~ (l1_pre_topc @ X36))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.46/0.68  thf('6', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_4))),
% 0.46/0.68      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.68  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('8', plain, ((l1_pre_topc @ sk_C_4)),
% 0.46/0.68      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.68  thf('9', plain,
% 0.46/0.68      ((m1_subset_1 @ (u1_struct_0 @ sk_B_1) @ 
% 0.46/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_4)))),
% 0.46/0.68      inference('demod', [status(thm)], ['3', '8'])).
% 0.46/0.68  thf(t2_subset, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( m1_subset_1 @ A @ B ) =>
% 0.46/0.68       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.46/0.68  thf('10', plain,
% 0.46/0.68      (![X32 : $i, X33 : $i]:
% 0.46/0.68         ((r2_hidden @ X32 @ X33)
% 0.46/0.68          | (v1_xboole_0 @ X33)
% 0.46/0.68          | ~ (m1_subset_1 @ X32 @ X33))),
% 0.46/0.68      inference('cnf', [status(esa)], [t2_subset])).
% 0.46/0.68  thf('11', plain,
% 0.46/0.68      (((v1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_4)))
% 0.46/0.68        | (r2_hidden @ (u1_struct_0 @ sk_B_1) @ 
% 0.46/0.68           (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_4))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.68  thf(d10_xboole_0, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.68  thf('12', plain,
% 0.46/0.68      (![X17 : $i, X18 : $i]: ((r1_tarski @ X17 @ X18) | ((X17) != (X18)))),
% 0.46/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.68  thf('13', plain, (![X18 : $i]: (r1_tarski @ X18 @ X18)),
% 0.46/0.68      inference('simplify', [status(thm)], ['12'])).
% 0.46/0.68  thf(d1_zfmisc_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.46/0.68       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.46/0.68  thf('14', plain,
% 0.46/0.68      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.46/0.68         (~ (r1_tarski @ X24 @ X25)
% 0.46/0.68          | (r2_hidden @ X24 @ X26)
% 0.46/0.68          | ((X26) != (k1_zfmisc_1 @ X25)))),
% 0.46/0.68      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.46/0.68  thf('15', plain,
% 0.46/0.68      (![X24 : $i, X25 : $i]:
% 0.46/0.68         ((r2_hidden @ X24 @ (k1_zfmisc_1 @ X25)) | ~ (r1_tarski @ X24 @ X25))),
% 0.46/0.68      inference('simplify', [status(thm)], ['14'])).
% 0.46/0.68  thf('16', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['13', '15'])).
% 0.46/0.68  thf(d1_xboole_0, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.46/0.68  thf('17', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.68      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.68  thf('18', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.68  thf('19', plain,
% 0.46/0.68      ((r2_hidden @ (u1_struct_0 @ sk_B_1) @ 
% 0.46/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_4)))),
% 0.46/0.68      inference('clc', [status(thm)], ['11', '18'])).
% 0.46/0.68  thf('20', plain,
% 0.46/0.68      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X27 @ X26)
% 0.46/0.68          | (r1_tarski @ X27 @ X25)
% 0.46/0.68          | ((X26) != (k1_zfmisc_1 @ X25)))),
% 0.46/0.68      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.46/0.68  thf('21', plain,
% 0.46/0.68      (![X25 : $i, X27 : $i]:
% 0.46/0.68         ((r1_tarski @ X27 @ X25) | ~ (r2_hidden @ X27 @ (k1_zfmisc_1 @ X25)))),
% 0.46/0.68      inference('simplify', [status(thm)], ['20'])).
% 0.46/0.68  thf('22', plain,
% 0.46/0.68      ((r1_tarski @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_4))),
% 0.46/0.68      inference('sup-', [status(thm)], ['19', '21'])).
% 0.46/0.68  thf(t28_xboole_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.46/0.68  thf('23', plain,
% 0.46/0.68      (![X20 : $i, X21 : $i]:
% 0.46/0.68         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.46/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.68  thf('24', plain,
% 0.46/0.68      (((k3_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_4))
% 0.46/0.68         = (u1_struct_0 @ sk_B_1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.68  thf('25', plain,
% 0.46/0.68      (![X34 : $i]: ((l1_struct_0 @ X34) | ~ (l1_pre_topc @ X34))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.68  thf('26', plain,
% 0.46/0.68      (![X34 : $i]: ((l1_struct_0 @ X34) | ~ (l1_pre_topc @ X34))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.68  thf('27', plain,
% 0.46/0.68      (![X34 : $i]: ((l1_struct_0 @ X34) | ~ (l1_pre_topc @ X34))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.68  thf('28', plain,
% 0.46/0.68      (![X34 : $i]: ((l1_struct_0 @ X34) | ~ (l1_pre_topc @ X34))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.68  thf('29', plain,
% 0.46/0.68      (((r1_tsep_1 @ sk_B_1 @ sk_C_4) | (r1_tsep_1 @ sk_C_4 @ sk_B_1))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('30', plain,
% 0.46/0.68      (((r1_tsep_1 @ sk_C_4 @ sk_B_1)) <= (((r1_tsep_1 @ sk_C_4 @ sk_B_1)))),
% 0.46/0.68      inference('split', [status(esa)], ['29'])).
% 0.46/0.68  thf(symmetry_r1_tsep_1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.46/0.68       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.46/0.68  thf('31', plain,
% 0.46/0.68      (![X40 : $i, X41 : $i]:
% 0.46/0.68         (~ (l1_struct_0 @ X40)
% 0.46/0.68          | ~ (l1_struct_0 @ X41)
% 0.46/0.68          | (r1_tsep_1 @ X41 @ X40)
% 0.46/0.68          | ~ (r1_tsep_1 @ X40 @ X41))),
% 0.46/0.68      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.46/0.68  thf('32', plain,
% 0.46/0.68      ((((r1_tsep_1 @ sk_B_1 @ sk_C_4)
% 0.46/0.68         | ~ (l1_struct_0 @ sk_B_1)
% 0.46/0.68         | ~ (l1_struct_0 @ sk_C_4))) <= (((r1_tsep_1 @ sk_C_4 @ sk_B_1)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['30', '31'])).
% 0.46/0.68  thf('33', plain,
% 0.46/0.68      (((~ (l1_pre_topc @ sk_B_1)
% 0.46/0.68         | ~ (l1_struct_0 @ sk_C_4)
% 0.46/0.68         | (r1_tsep_1 @ sk_B_1 @ sk_C_4))) <= (((r1_tsep_1 @ sk_C_4 @ sk_B_1)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['28', '32'])).
% 0.46/0.68  thf('34', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('35', plain,
% 0.46/0.68      (![X35 : $i, X36 : $i]:
% 0.46/0.68         (~ (m1_pre_topc @ X35 @ X36)
% 0.46/0.68          | (l1_pre_topc @ X35)
% 0.46/0.68          | ~ (l1_pre_topc @ X36))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.46/0.68  thf('36', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B_1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.68  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('38', plain, ((l1_pre_topc @ sk_B_1)),
% 0.46/0.68      inference('demod', [status(thm)], ['36', '37'])).
% 0.46/0.68  thf('39', plain,
% 0.46/0.68      (((~ (l1_struct_0 @ sk_C_4) | (r1_tsep_1 @ sk_B_1 @ sk_C_4)))
% 0.46/0.68         <= (((r1_tsep_1 @ sk_C_4 @ sk_B_1)))),
% 0.46/0.68      inference('demod', [status(thm)], ['33', '38'])).
% 0.46/0.68  thf('40', plain,
% 0.46/0.68      (((~ (l1_pre_topc @ sk_C_4) | (r1_tsep_1 @ sk_B_1 @ sk_C_4)))
% 0.46/0.68         <= (((r1_tsep_1 @ sk_C_4 @ sk_B_1)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['27', '39'])).
% 0.46/0.68  thf('41', plain, ((l1_pre_topc @ sk_C_4)),
% 0.46/0.68      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.68  thf('42', plain,
% 0.46/0.68      (((r1_tsep_1 @ sk_B_1 @ sk_C_4)) <= (((r1_tsep_1 @ sk_C_4 @ sk_B_1)))),
% 0.46/0.68      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.68  thf(d3_tsep_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( l1_struct_0 @ A ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( l1_struct_0 @ B ) =>
% 0.46/0.68           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.46/0.68             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.46/0.68  thf('43', plain,
% 0.46/0.68      (![X38 : $i, X39 : $i]:
% 0.46/0.68         (~ (l1_struct_0 @ X38)
% 0.46/0.68          | ~ (r1_tsep_1 @ X39 @ X38)
% 0.46/0.68          | (r1_xboole_0 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X38))
% 0.46/0.68          | ~ (l1_struct_0 @ X39))),
% 0.46/0.68      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.46/0.68  thf('44', plain,
% 0.46/0.68      (((~ (l1_struct_0 @ sk_B_1)
% 0.46/0.68         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_4))
% 0.46/0.68         | ~ (l1_struct_0 @ sk_C_4))) <= (((r1_tsep_1 @ sk_C_4 @ sk_B_1)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['42', '43'])).
% 0.46/0.68  thf('45', plain,
% 0.46/0.68      (((~ (l1_pre_topc @ sk_B_1)
% 0.46/0.68         | ~ (l1_struct_0 @ sk_C_4)
% 0.46/0.68         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_4))))
% 0.46/0.68         <= (((r1_tsep_1 @ sk_C_4 @ sk_B_1)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['26', '44'])).
% 0.46/0.68  thf('46', plain, ((l1_pre_topc @ sk_B_1)),
% 0.46/0.68      inference('demod', [status(thm)], ['36', '37'])).
% 0.46/0.68  thf('47', plain,
% 0.46/0.68      (((~ (l1_struct_0 @ sk_C_4)
% 0.46/0.68         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_4))))
% 0.46/0.68         <= (((r1_tsep_1 @ sk_C_4 @ sk_B_1)))),
% 0.46/0.68      inference('demod', [status(thm)], ['45', '46'])).
% 0.46/0.68  thf('48', plain,
% 0.46/0.68      (((~ (l1_pre_topc @ sk_C_4)
% 0.46/0.68         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_4))))
% 0.46/0.68         <= (((r1_tsep_1 @ sk_C_4 @ sk_B_1)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['25', '47'])).
% 0.46/0.68  thf('49', plain, ((l1_pre_topc @ sk_C_4)),
% 0.46/0.68      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.68  thf('50', plain,
% 0.46/0.68      (((r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_4)))
% 0.46/0.68         <= (((r1_tsep_1 @ sk_C_4 @ sk_B_1)))),
% 0.46/0.68      inference('demod', [status(thm)], ['48', '49'])).
% 0.46/0.68  thf('51', plain,
% 0.46/0.68      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.46/0.68      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.68  thf(t4_xboole_0, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.68            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.68       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.46/0.68            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.46/0.68  thf('52', plain,
% 0.46/0.68      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X15 @ (k3_xboole_0 @ X13 @ X16))
% 0.46/0.68          | ~ (r1_xboole_0 @ X13 @ X16))),
% 0.46/0.68      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.68  thf('53', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['51', '52'])).
% 0.46/0.68  thf('54', plain,
% 0.46/0.68      (((v1_xboole_0 @ 
% 0.46/0.68         (k3_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_4))))
% 0.46/0.68         <= (((r1_tsep_1 @ sk_C_4 @ sk_B_1)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['50', '53'])).
% 0.46/0.68  thf(d3_tarski, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.68       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.68  thf('55', plain,
% 0.46/0.68      (![X4 : $i, X6 : $i]:
% 0.46/0.68         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.46/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.68  thf('56', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.68      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.68  thf('57', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['55', '56'])).
% 0.46/0.68  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.68  thf('58', plain, (![X22 : $i]: (r1_tarski @ k1_xboole_0 @ X22)),
% 0.46/0.68      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.68  thf('59', plain,
% 0.46/0.68      (![X17 : $i, X19 : $i]:
% 0.46/0.68         (((X17) = (X19))
% 0.46/0.68          | ~ (r1_tarski @ X19 @ X17)
% 0.46/0.68          | ~ (r1_tarski @ X17 @ X19))),
% 0.46/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.68  thf('60', plain,
% 0.46/0.68      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['58', '59'])).
% 0.46/0.68  thf('61', plain,
% 0.46/0.68      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['57', '60'])).
% 0.46/0.68  thf('62', plain,
% 0.46/0.68      ((((k3_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_4))
% 0.46/0.68          = (k1_xboole_0)))
% 0.46/0.68         <= (((r1_tsep_1 @ sk_C_4 @ sk_B_1)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['54', '61'])).
% 0.46/0.68  thf('63', plain,
% 0.46/0.68      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))
% 0.46/0.68         <= (((r1_tsep_1 @ sk_C_4 @ sk_B_1)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['24', '62'])).
% 0.46/0.68  thf('64', plain,
% 0.46/0.68      (![X34 : $i]: ((l1_struct_0 @ X34) | ~ (l1_pre_topc @ X34))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.68  thf('65', plain,
% 0.46/0.68      (((k3_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_4))
% 0.46/0.68         = (u1_struct_0 @ sk_B_1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.68  thf('66', plain,
% 0.46/0.68      (![X34 : $i]: ((l1_struct_0 @ X34) | ~ (l1_pre_topc @ X34))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.68  thf('67', plain,
% 0.46/0.68      (![X34 : $i]: ((l1_struct_0 @ X34) | ~ (l1_pre_topc @ X34))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.46/0.68  thf('68', plain,
% 0.46/0.68      (((r1_tsep_1 @ sk_B_1 @ sk_C_4)) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_4)))),
% 0.46/0.68      inference('split', [status(esa)], ['29'])).
% 0.46/0.68  thf('69', plain,
% 0.46/0.68      (![X38 : $i, X39 : $i]:
% 0.46/0.68         (~ (l1_struct_0 @ X38)
% 0.46/0.68          | ~ (r1_tsep_1 @ X39 @ X38)
% 0.46/0.68          | (r1_xboole_0 @ (u1_struct_0 @ X39) @ (u1_struct_0 @ X38))
% 0.46/0.68          | ~ (l1_struct_0 @ X39))),
% 0.46/0.68      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.46/0.68  thf('70', plain,
% 0.46/0.68      (((~ (l1_struct_0 @ sk_B_1)
% 0.46/0.68         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_4))
% 0.46/0.68         | ~ (l1_struct_0 @ sk_C_4))) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_4)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['68', '69'])).
% 0.46/0.68  thf('71', plain,
% 0.46/0.68      (((~ (l1_pre_topc @ sk_B_1)
% 0.46/0.68         | ~ (l1_struct_0 @ sk_C_4)
% 0.46/0.68         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_4))))
% 0.46/0.68         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_4)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['67', '70'])).
% 0.46/0.68  thf('72', plain, ((l1_pre_topc @ sk_B_1)),
% 0.46/0.68      inference('demod', [status(thm)], ['36', '37'])).
% 0.46/0.68  thf('73', plain,
% 0.46/0.68      (((~ (l1_struct_0 @ sk_C_4)
% 0.46/0.68         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_4))))
% 0.46/0.68         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_4)))),
% 0.46/0.68      inference('demod', [status(thm)], ['71', '72'])).
% 0.46/0.68  thf('74', plain,
% 0.46/0.68      (((~ (l1_pre_topc @ sk_C_4)
% 0.46/0.68         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_4))))
% 0.46/0.68         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_4)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['66', '73'])).
% 0.46/0.68  thf('75', plain, ((l1_pre_topc @ sk_C_4)),
% 0.46/0.68      inference('demod', [status(thm)], ['6', '7'])).
% 0.46/0.68  thf('76', plain,
% 0.46/0.68      (((r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_4)))
% 0.46/0.68         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_4)))),
% 0.46/0.68      inference('demod', [status(thm)], ['74', '75'])).
% 0.46/0.68  thf('77', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['51', '52'])).
% 0.46/0.68  thf('78', plain,
% 0.46/0.68      (((v1_xboole_0 @ 
% 0.46/0.68         (k3_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_4))))
% 0.46/0.68         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_4)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['76', '77'])).
% 0.46/0.68  thf('79', plain,
% 0.46/0.68      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['57', '60'])).
% 0.46/0.68  thf('80', plain,
% 0.46/0.68      ((((k3_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_4))
% 0.46/0.68          = (k1_xboole_0)))
% 0.46/0.68         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_4)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['78', '79'])).
% 0.46/0.68  thf('81', plain,
% 0.46/0.68      ((((u1_struct_0 @ sk_B_1) = (k1_xboole_0)))
% 0.46/0.68         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_4)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['65', '80'])).
% 0.46/0.68  thf(fc2_struct_0, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.68       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.68  thf('82', plain,
% 0.46/0.68      (![X37 : $i]:
% 0.46/0.68         (~ (v1_xboole_0 @ (u1_struct_0 @ X37))
% 0.46/0.68          | ~ (l1_struct_0 @ X37)
% 0.46/0.68          | (v2_struct_0 @ X37))),
% 0.46/0.68      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.46/0.68  thf('83', plain,
% 0.46/0.68      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.68         | (v2_struct_0 @ sk_B_1)
% 0.46/0.68         | ~ (l1_struct_0 @ sk_B_1))) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_4)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['81', '82'])).
% 0.46/0.68  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.46/0.68  thf('84', plain, (![X23 : $i]: (r1_xboole_0 @ X23 @ k1_xboole_0)),
% 0.46/0.68      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.46/0.68  thf('85', plain,
% 0.46/0.68      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.46/0.68      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.68  thf('86', plain, (![X18 : $i]: (r1_tarski @ X18 @ X18)),
% 0.46/0.68      inference('simplify', [status(thm)], ['12'])).
% 0.46/0.68  thf('87', plain,
% 0.46/0.68      (![X20 : $i, X21 : $i]:
% 0.46/0.68         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.46/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.46/0.68  thf('88', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['86', '87'])).
% 0.46/0.68  thf('89', plain,
% 0.46/0.68      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X15 @ (k3_xboole_0 @ X13 @ X16))
% 0.46/0.68          | ~ (r1_xboole_0 @ X13 @ X16))),
% 0.46/0.68      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.46/0.68  thf('90', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['88', '89'])).
% 0.46/0.68  thf('91', plain,
% 0.46/0.68      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['85', '90'])).
% 0.46/0.68  thf('92', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.68      inference('sup-', [status(thm)], ['84', '91'])).
% 0.46/0.68  thf('93', plain,
% 0.46/0.68      ((((v2_struct_0 @ sk_B_1) | ~ (l1_struct_0 @ sk_B_1)))
% 0.46/0.68         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_4)))),
% 0.46/0.68      inference('demod', [status(thm)], ['83', '92'])).
% 0.46/0.68  thf('94', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('95', plain,
% 0.46/0.68      ((~ (l1_struct_0 @ sk_B_1)) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_4)))),
% 0.46/0.68      inference('clc', [status(thm)], ['93', '94'])).
% 0.46/0.68  thf('96', plain,
% 0.46/0.68      ((~ (l1_pre_topc @ sk_B_1)) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_4)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['64', '95'])).
% 0.46/0.68  thf('97', plain, ((l1_pre_topc @ sk_B_1)),
% 0.46/0.68      inference('demod', [status(thm)], ['36', '37'])).
% 0.46/0.68  thf('98', plain, (~ ((r1_tsep_1 @ sk_B_1 @ sk_C_4))),
% 0.46/0.68      inference('demod', [status(thm)], ['96', '97'])).
% 0.46/0.68  thf('99', plain,
% 0.46/0.68      (((r1_tsep_1 @ sk_C_4 @ sk_B_1)) | ((r1_tsep_1 @ sk_B_1 @ sk_C_4))),
% 0.46/0.68      inference('split', [status(esa)], ['29'])).
% 0.46/0.68  thf('100', plain, (((r1_tsep_1 @ sk_C_4 @ sk_B_1))),
% 0.46/0.68      inference('sat_resolution*', [status(thm)], ['98', '99'])).
% 0.46/0.68  thf('101', plain, (((u1_struct_0 @ sk_B_1) = (k1_xboole_0))),
% 0.46/0.68      inference('simpl_trail', [status(thm)], ['63', '100'])).
% 0.46/0.68  thf('102', plain,
% 0.46/0.68      (![X37 : $i]:
% 0.46/0.68         (~ (v1_xboole_0 @ (u1_struct_0 @ X37))
% 0.46/0.68          | ~ (l1_struct_0 @ X37)
% 0.46/0.68          | (v2_struct_0 @ X37))),
% 0.46/0.68      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.46/0.68  thf('103', plain,
% 0.46/0.68      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.68        | (v2_struct_0 @ sk_B_1)
% 0.46/0.68        | ~ (l1_struct_0 @ sk_B_1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['101', '102'])).
% 0.46/0.68  thf('104', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.68      inference('sup-', [status(thm)], ['84', '91'])).
% 0.46/0.68  thf('105', plain, (((v2_struct_0 @ sk_B_1) | ~ (l1_struct_0 @ sk_B_1))),
% 0.46/0.68      inference('demod', [status(thm)], ['103', '104'])).
% 0.46/0.68  thf('106', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('107', plain, (~ (l1_struct_0 @ sk_B_1)),
% 0.46/0.68      inference('clc', [status(thm)], ['105', '106'])).
% 0.46/0.68  thf('108', plain, (~ (l1_pre_topc @ sk_B_1)),
% 0.46/0.68      inference('sup-', [status(thm)], ['0', '107'])).
% 0.46/0.68  thf('109', plain, ((l1_pre_topc @ sk_B_1)),
% 0.46/0.68      inference('demod', [status(thm)], ['36', '37'])).
% 0.46/0.68  thf('110', plain, ($false), inference('demod', [status(thm)], ['108', '109'])).
% 0.46/0.68  
% 0.46/0.68  % SZS output end Refutation
% 0.46/0.68  
% 0.46/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
