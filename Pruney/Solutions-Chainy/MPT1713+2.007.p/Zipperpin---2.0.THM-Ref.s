%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iQPHwfcFeF

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 313 expanded)
%              Number of leaves         :   33 ( 107 expanded)
%              Depth                    :   23
%              Number of atoms          :  684 (3186 expanded)
%              Number of equality atoms :   10 (  18 expanded)
%              Maximal formula depth    :   18 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    m1_pre_topc @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ B @ A )
          <=> ( ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) )
                  <=> ? [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                        & ( r2_hidden @ D @ ( u1_pre_topc @ A ) )
                        & ( C
                          = ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) )
              & ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
    <=> ( ( C
          = ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) )
        & ( r2_hidden @ D @ ( u1_pre_topc @ A ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ B @ A )
          <=> ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) )
                  <=> ? [D: $i] :
                        ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ( r1_tarski @ ( k2_struct_0 @ X12 ) @ ( k2_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
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

thf('15',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['4','9','14'])).

thf('16',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('17',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( r1_tsep_1 @ sk_C_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_B )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_struct_0 @ X23 )
      | ~ ( l1_struct_0 @ X24 )
      | ( r1_tsep_1 @ X24 @ X23 )
      | ~ ( r1_tsep_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('20',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['12','13'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('22',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('23',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('25',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('26',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['20','23','26'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('28',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_struct_0 @ X21 )
      | ~ ( r1_tsep_1 @ X22 @ X21 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('29',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf('31',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('32',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf(t68_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ~ ( ( r1_tarski @ C @ A )
          & ( r1_tarski @ C @ B )
          & ( r1_xboole_0 @ A @ B ) ) ) )).

thf('33',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_xboole_0 @ X3 @ X4 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t68_xboole_1])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_B ) )
        | ( v1_xboole_0 @ X0 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ ( k2_struct_0 @ sk_C_1 ) )
        | ~ ( l1_struct_0 @ sk_C_1 )
        | ( v1_xboole_0 @ X0 )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_B ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ ( k2_struct_0 @ sk_C_1 ) )
        | ( v1_xboole_0 @ X0 )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_B ) ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('39',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['4','9','14'])).

thf('40',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('41',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['17'])).

thf('42',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_struct_0 @ X21 )
      | ~ ( r1_tsep_1 @ X22 @ X21 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('43',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf('45',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('46',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['40','46'])).

thf('48',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('49',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_xboole_0 @ X3 @ X4 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t68_xboole_1])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ ( k2_struct_0 @ sk_C_1 ) )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_B ) )
        | ( v1_xboole_0 @ X0 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
      | ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['39','51'])).

thf('53',plain,
    ( ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B )
      | ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['38','52'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['53','55','56'])).

thf('58',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('59',plain,(
    ! [X20: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['57','61'])).

thf('63',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['17'])).

thf('68',plain,(
    r1_tsep_1 @ sk_C_1 @ sk_B ),
    inference('sat_resolution*',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_struct_0 @ sk_C_1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['37','68'])).

thf('70',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','69'])).

thf('71',plain,
    ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','70'])).

thf('72',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['54'])).

thf('73',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf('74',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('76',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf('78',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['0','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iQPHwfcFeF
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:49:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 129 iterations in 0.048s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.50  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.50  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.50  thf(t22_tmap_1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.50               ( ( m1_pre_topc @ B @ C ) =>
% 0.20/0.50                 ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.50            ( l1_pre_topc @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.50              ( ![C:$i]:
% 0.20/0.50                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.50                  ( ( m1_pre_topc @ B @ C ) =>
% 0.20/0.50                    ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t22_tmap_1])).
% 0.20/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d3_struct_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X6 : $i]:
% 0.20/0.50         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.50  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d9_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( l1_pre_topc @ B ) =>
% 0.20/0.50           ( ( m1_pre_topc @ B @ A ) <=>
% 0.20/0.50             ( ( ![C:$i]:
% 0.20/0.50                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.50                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.20/0.50                     ( ?[D:$i]:
% 0.20/0.50                       ( ( m1_subset_1 @
% 0.20/0.50                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.20/0.50                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.20/0.50                         ( ( C ) =
% 0.20/0.50                           ( k9_subset_1 @
% 0.20/0.50                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 0.20/0.50               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.50  thf(zf_stmt_2, axiom,
% 0.20/0.50    (![D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.50     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.20/0.50       ( ( ( C ) =
% 0.20/0.50           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 0.20/0.50         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.20/0.50         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_3, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( l1_pre_topc @ B ) =>
% 0.20/0.50           ( ( m1_pre_topc @ B @ A ) <=>
% 0.20/0.50             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 0.20/0.50               ( ![C:$i]:
% 0.20/0.50                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.50                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.20/0.50                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X12 : $i, X13 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X12)
% 0.20/0.50          | ~ (m1_pre_topc @ X12 @ X13)
% 0.20/0.50          | (r1_tarski @ (k2_struct_0 @ X12) @ (k2_struct_0 @ X13))
% 0.20/0.50          | ~ (l1_pre_topc @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_C_1)
% 0.20/0.50        | (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))
% 0.20/0.50        | ~ (l1_pre_topc @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf('5', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_m1_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X18 : $i, X19 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X18 @ X19)
% 0.20/0.50          | (l1_pre_topc @ X18)
% 0.20/0.50          | ~ (l1_pre_topc @ X19))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.50  thf('7', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.50  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('9', plain, ((l1_pre_topc @ sk_C_1)),
% 0.20/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf('10', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X18 : $i, X19 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X18 @ X19)
% 0.20/0.50          | (l1_pre_topc @ X18)
% 0.20/0.50          | ~ (l1_pre_topc @ X19))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.50  thf('12', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('14', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      ((r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))),
% 0.20/0.50      inference('demod', [status(thm)], ['4', '9', '14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X6 : $i]:
% 0.20/0.50         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_B @ sk_C_1) | (r1_tsep_1 @ sk_C_1 @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_C_1 @ sk_B)) <= (((r1_tsep_1 @ sk_C_1 @ sk_B)))),
% 0.20/0.50      inference('split', [status(esa)], ['17'])).
% 0.20/0.50  thf(symmetry_r1_tsep_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.20/0.50       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X23 : $i, X24 : $i]:
% 0.20/0.50         (~ (l1_struct_0 @ X23)
% 0.20/0.50          | ~ (l1_struct_0 @ X24)
% 0.20/0.50          | (r1_tsep_1 @ X24 @ X23)
% 0.20/0.50          | ~ (r1_tsep_1 @ X23 @ X24))),
% 0.20/0.50      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      ((((r1_tsep_1 @ sk_B @ sk_C_1)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_B)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('21', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf(dt_l1_pre_topc, axiom,
% 0.20/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('23', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('24', plain, ((l1_pre_topc @ sk_C_1)),
% 0.20/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('26', plain, ((l1_struct_0 @ sk_C_1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_B @ sk_C_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['20', '23', '26'])).
% 0.20/0.50  thf(d3_tsep_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_struct_0 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( l1_struct_0 @ B ) =>
% 0.20/0.50           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.20/0.50             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X21 : $i, X22 : $i]:
% 0.20/0.50         (~ (l1_struct_0 @ X21)
% 0.20/0.50          | ~ (r1_tsep_1 @ X22 @ X21)
% 0.20/0.50          | (r1_xboole_0 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))
% 0.20/0.50          | ~ (l1_struct_0 @ X22))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_B)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))
% 0.20/0.50         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.50  thf('30', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('31', plain, ((l1_struct_0 @ sk_C_1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C_1 @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.20/0.50  thf(t68_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.50       ( ~( ( r1_tarski @ C @ A ) & ( r1_tarski @ C @ B ) & 
% 0.20/0.50            ( r1_xboole_0 @ A @ B ) ) ) ))).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.50         (~ (r1_xboole_0 @ X3 @ X4)
% 0.20/0.50          | (v1_xboole_0 @ X5)
% 0.20/0.50          | ~ (r1_tarski @ X5 @ X3)
% 0.20/0.50          | ~ (r1_tarski @ X5 @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [t68_xboole_1])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_C_1))
% 0.20/0.50           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_B))
% 0.20/0.50           | (v1_xboole_0 @ X0)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C_1 @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (~ (r1_tarski @ X0 @ (k2_struct_0 @ sk_C_1))
% 0.20/0.50           | ~ (l1_struct_0 @ sk_C_1)
% 0.20/0.50           | (v1_xboole_0 @ X0)
% 0.20/0.50           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_B))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C_1 @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['16', '34'])).
% 0.20/0.50  thf('36', plain, ((l1_struct_0 @ sk_C_1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (~ (r1_tarski @ X0 @ (k2_struct_0 @ sk_C_1))
% 0.20/0.50           | (v1_xboole_0 @ X0)
% 0.20/0.50           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_B))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C_1 @ sk_B)))),
% 0.20/0.50      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (![X6 : $i]:
% 0.20/0.50         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      ((r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))),
% 0.20/0.50      inference('demod', [status(thm)], ['4', '9', '14'])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (![X6 : $i]:
% 0.20/0.50         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_B @ sk_C_1)) <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.20/0.50      inference('split', [status(esa)], ['17'])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X21 : $i, X22 : $i]:
% 0.20/0.50         (~ (l1_struct_0 @ X21)
% 0.20/0.50          | ~ (r1_tsep_1 @ X22 @ X21)
% 0.20/0.50          | (r1_xboole_0 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))
% 0.20/0.50          | ~ (l1_struct_0 @ X22))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_B)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))
% 0.20/0.50         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.50  thf('44', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('45', plain, ((l1_struct_0 @ sk_C_1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      ((((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))
% 0.20/0.50         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['40', '46'])).
% 0.20/0.50  thf('48', plain, ((l1_struct_0 @ sk_C_1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.50         (~ (r1_xboole_0 @ X3 @ X4)
% 0.20/0.50          | (v1_xboole_0 @ X5)
% 0.20/0.50          | ~ (r1_tarski @ X5 @ X3)
% 0.20/0.50          | ~ (r1_tarski @ X5 @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [t68_xboole_1])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (~ (r1_tarski @ X0 @ (k2_struct_0 @ sk_C_1))
% 0.20/0.50           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_B))
% 0.20/0.50           | (v1_xboole_0 @ X0)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      ((((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.20/0.50         | ~ (r1_tarski @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['39', '51'])).
% 0.20/0.50  thf('53', plain,
% 0.20/0.50      (((~ (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_B))
% 0.20/0.50         | ~ (l1_struct_0 @ sk_B)
% 0.20/0.50         | (v1_xboole_0 @ (k2_struct_0 @ sk_B))))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['38', '52'])).
% 0.20/0.50  thf(d10_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.50  thf('55', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.50      inference('simplify', [status(thm)], ['54'])).
% 0.20/0.50  thf('56', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      (((v1_xboole_0 @ (k2_struct_0 @ sk_B)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['53', '55', '56'])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      (![X6 : $i]:
% 0.20/0.50         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.50  thf(fc2_struct_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.50       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      (![X20 : $i]:
% 0.20/0.50         (~ (v1_xboole_0 @ (u1_struct_0 @ X20))
% 0.20/0.50          | ~ (l1_struct_0 @ X20)
% 0.20/0.50          | (v2_struct_0 @ X20))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.50  thf('60', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.20/0.50          | ~ (l1_struct_0 @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | ~ (l1_struct_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (l1_struct_0 @ X0)
% 0.20/0.50          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['60'])).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_B) | (v2_struct_0 @ sk_B)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['57', '61'])).
% 0.20/0.50  thf('63', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('64', plain, (((v2_struct_0 @ sk_B)) <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['62', '63'])).
% 0.20/0.50  thf('65', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('66', plain, (~ ((r1_tsep_1 @ sk_B @ sk_C_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_C_1 @ sk_B)) | ((r1_tsep_1 @ sk_B @ sk_C_1))),
% 0.20/0.50      inference('split', [status(esa)], ['17'])).
% 0.20/0.50  thf('68', plain, (((r1_tsep_1 @ sk_C_1 @ sk_B))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['66', '67'])).
% 0.20/0.50  thf('69', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r1_tarski @ X0 @ (k2_struct_0 @ sk_C_1))
% 0.20/0.50          | (v1_xboole_0 @ X0)
% 0.20/0.50          | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['37', '68'])).
% 0.20/0.50  thf('70', plain,
% 0.20/0.50      ((~ (r1_tarski @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.20/0.50        | (v1_xboole_0 @ (k2_struct_0 @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '69'])).
% 0.20/0.50  thf('71', plain,
% 0.20/0.50      ((~ (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_B))
% 0.20/0.50        | ~ (l1_struct_0 @ sk_B)
% 0.20/0.50        | (v1_xboole_0 @ (k2_struct_0 @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '70'])).
% 0.20/0.50  thf('72', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.50      inference('simplify', [status(thm)], ['54'])).
% 0.20/0.50  thf('73', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('74', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.20/0.50  thf('75', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (l1_struct_0 @ X0)
% 0.20/0.50          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['60'])).
% 0.20/0.50  thf('76', plain, ((~ (l1_struct_0 @ sk_B) | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['74', '75'])).
% 0.20/0.50  thf('77', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('78', plain, ((v2_struct_0 @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['76', '77'])).
% 0.20/0.50  thf('79', plain, ($false), inference('demod', [status(thm)], ['0', '78'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
