%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.buqVNXs82T

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 649 expanded)
%              Number of leaves         :   33 ( 206 expanded)
%              Depth                    :   17
%              Number of atoms          :  793 (8845 expanded)
%              Number of equality atoms :    9 (  30 expanded)
%              Maximal formula depth    :   18 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('1',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['1'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( r1_tsep_1 @ X21 @ X20 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('4',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
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
    | ( l1_pre_topc @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['7','8'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('10',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('11',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('18',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['4','11','18'])).

thf('20',plain,
    ( ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['0','19'])).

thf('21',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('22',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
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

thf('24',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ( r1_tarski @ ( k2_struct_0 @ X12 ) @ ( k2_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('27',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['25','26','31'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('34',plain,
    ( ( k2_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('35',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','36'])).

thf('38',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('39',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ( r1_tsep_1 @ X21 @ X20 )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( u1_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r1_tsep_1 @ X1 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tsep_1 @ X1 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_2 )
      | ( r1_tsep_1 @ sk_D_2 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['37','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['29','30'])).

thf('44',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('45',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('47',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['42','45','46'])).

thf('48',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
    | ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('52',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['1'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('53',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_struct_0 @ X22 )
      | ~ ( l1_struct_0 @ X23 )
      | ( r1_tsep_1 @ X23 @ X22 )
      | ~ ( r1_tsep_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('54',plain,
    ( ( ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('56',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('57',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( r1_tsep_1 @ X21 @ X20 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('59',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('61',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('62',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['51','62'])).

thf('64',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('65',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('67',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tsep_1 @ X1 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('69',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_2 )
      | ( r1_tsep_1 @ sk_D_2 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['43','44'])).

thf('71',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('72',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_struct_0 @ X22 )
      | ~ ( l1_struct_0 @ X23 )
      | ( r1_tsep_1 @ X23 @ X22 )
      | ~ ( r1_tsep_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('74',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['43','44'])).

thf('76',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('77',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['48'])).

thf('79',plain,
    ( ~ ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['42','45','46'])).

thf('81',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_struct_0 @ X22 )
      | ~ ( l1_struct_0 @ X23 )
      | ( r1_tsep_1 @ X23 @ X22 )
      | ~ ( r1_tsep_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('82',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['43','44'])).

thf('84',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('85',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['48'])).

thf('87',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
    | ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['48'])).

thf('89',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('90',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['48'])).

thf('91',plain,
    ( ~ ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['1'])).

thf('93',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['50','79','87','88','91','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.buqVNXs82T
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:24:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 84 iterations in 0.034s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.52  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.52  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.21/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.21/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.52  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.52  thf(d3_struct_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (![X6 : $i]:
% 0.21/0.52         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.52  thf(t24_tmap_1, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.52               ( ![D:$i]:
% 0.21/0.52                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.52                   ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.52                     ( ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.21/0.52                         ( ~( r1_tsep_1 @ D @ C ) ) ) | 
% 0.21/0.52                       ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.52            ( l1_pre_topc @ A ) ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.52              ( ![C:$i]:
% 0.21/0.52                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.52                  ( ![D:$i]:
% 0.21/0.52                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.21/0.52                      ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.52                        ( ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.21/0.52                            ( ~( r1_tsep_1 @ D @ C ) ) ) | 
% 0.21/0.52                          ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t24_tmap_1])).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (((r1_tsep_1 @ sk_C_1 @ sk_D_2) | (r1_tsep_1 @ sk_D_2 @ sk_C_1))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (((r1_tsep_1 @ sk_D_2 @ sk_C_1)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.21/0.52      inference('split', [status(esa)], ['1'])).
% 0.21/0.52  thf(d3_tsep_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_struct_0 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( l1_struct_0 @ B ) =>
% 0.21/0.52           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.21/0.52             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i]:
% 0.21/0.52         (~ (l1_struct_0 @ X20)
% 0.21/0.52          | ~ (r1_tsep_1 @ X21 @ X20)
% 0.21/0.52          | (r1_xboole_0 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.21/0.52          | ~ (l1_struct_0 @ X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (((~ (l1_struct_0 @ sk_D_2)
% 0.21/0.52         | (r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.52         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf('5', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_m1_pre_topc, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X18 : $i, X19 : $i]:
% 0.21/0.52         (~ (m1_pre_topc @ X18 @ X19)
% 0.21/0.52          | (l1_pre_topc @ X18)
% 0.21/0.52          | ~ (l1_pre_topc @ X19))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.52  thf('7', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D_2))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('9', plain, ((l1_pre_topc @ sk_D_2)),
% 0.21/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf(dt_l1_pre_topc, axiom,
% 0.21/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.52  thf('11', plain, ((l1_struct_0 @ sk_D_2)),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('12', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X18 : $i, X19 : $i]:
% 0.21/0.52         (~ (m1_pre_topc @ X18 @ X19)
% 0.21/0.52          | (l1_pre_topc @ X18)
% 0.21/0.52          | ~ (l1_pre_topc @ X19))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.52  thf('14', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.52  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('16', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.52  thf('18', plain, ((l1_struct_0 @ sk_C_1)),
% 0.21/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.52         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.21/0.52      inference('demod', [status(thm)], ['4', '11', '18'])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      ((((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1))
% 0.21/0.52         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['0', '19'])).
% 0.21/0.52  thf('21', plain, ((l1_struct_0 @ sk_C_1)),
% 0.21/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1)))
% 0.21/0.52         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.21/0.52      inference('demod', [status(thm)], ['20', '21'])).
% 0.21/0.52  thf('23', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d9_pre_topc, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( l1_pre_topc @ B ) =>
% 0.21/0.52           ( ( m1_pre_topc @ B @ A ) <=>
% 0.21/0.52             ( ( ![C:$i]:
% 0.21/0.52                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.52                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.21/0.52                     ( ?[D:$i]:
% 0.21/0.52                       ( ( m1_subset_1 @
% 0.21/0.52                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.52                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.21/0.52                         ( ( C ) =
% 0.21/0.52                           ( k9_subset_1 @
% 0.21/0.52                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 0.21/0.52               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.52  thf(zf_stmt_2, axiom,
% 0.21/0.52    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.52     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.21/0.52       ( ( ( C ) =
% 0.21/0.52           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 0.21/0.52         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.21/0.52         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_3, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( l1_pre_topc @ B ) =>
% 0.21/0.52           ( ( m1_pre_topc @ B @ A ) <=>
% 0.21/0.52             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 0.21/0.52               ( ![C:$i]:
% 0.21/0.52                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.52                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.21/0.52                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X12)
% 0.21/0.52          | ~ (m1_pre_topc @ X12 @ X13)
% 0.21/0.52          | (r1_tarski @ (k2_struct_0 @ X12) @ (k2_struct_0 @ X13))
% 0.21/0.52          | ~ (l1_pre_topc @ X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_C_1)
% 0.21/0.52        | (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))
% 0.21/0.52        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf('26', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.52      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf('27', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      (![X18 : $i, X19 : $i]:
% 0.21/0.52         (~ (m1_pre_topc @ X18 @ X19)
% 0.21/0.52          | (l1_pre_topc @ X18)
% 0.21/0.52          | ~ (l1_pre_topc @ X19))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.52  thf('29', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.52  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('31', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      ((r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['25', '26', '31'])).
% 0.21/0.52  thf(t12_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (((k2_xboole_0 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))
% 0.21/0.52         = (k2_struct_0 @ sk_C_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.52  thf(t70_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.21/0.52            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.21/0.52       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.21/0.52            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ X2 @ X3)
% 0.21/0.52          | ~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X5)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_C_1))
% 0.21/0.52          | (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B)))
% 0.21/0.52         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['22', '36'])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (![X6 : $i]:
% 0.21/0.52         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i]:
% 0.21/0.52         (~ (l1_struct_0 @ X20)
% 0.21/0.52          | ~ (r1_xboole_0 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.21/0.52          | (r1_tsep_1 @ X21 @ X20)
% 0.21/0.52          | ~ (l1_struct_0 @ X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (r1_xboole_0 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0))
% 0.21/0.52          | ~ (l1_struct_0 @ X0)
% 0.21/0.52          | ~ (l1_struct_0 @ X1)
% 0.21/0.52          | (r1_tsep_1 @ X1 @ X0)
% 0.21/0.52          | ~ (l1_struct_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r1_tsep_1 @ X1 @ X0)
% 0.21/0.52          | ~ (l1_struct_0 @ X1)
% 0.21/0.52          | ~ (l1_struct_0 @ X0)
% 0.21/0.52          | ~ (r1_xboole_0 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      (((~ (l1_struct_0 @ sk_B)
% 0.21/0.52         | ~ (l1_struct_0 @ sk_D_2)
% 0.21/0.52         | (r1_tsep_1 @ sk_D_2 @ sk_B))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['37', '41'])).
% 0.21/0.52  thf('43', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.52  thf('45', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.52  thf('46', plain, ((l1_struct_0 @ sk_D_2)),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (((r1_tsep_1 @ sk_D_2 @ sk_B)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.21/0.52      inference('demod', [status(thm)], ['42', '45', '46'])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      ((~ (r1_tsep_1 @ sk_B @ sk_D_2) | ~ (r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      ((~ (r1_tsep_1 @ sk_D_2 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)))),
% 0.21/0.52      inference('split', [status(esa)], ['48'])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (~ ((r1_tsep_1 @ sk_D_2 @ sk_C_1)) | ((r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['47', '49'])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      (![X6 : $i]:
% 0.21/0.52         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.52  thf('52', plain,
% 0.21/0.52      (((r1_tsep_1 @ sk_C_1 @ sk_D_2)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.21/0.52      inference('split', [status(esa)], ['1'])).
% 0.21/0.52  thf(symmetry_r1_tsep_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.21/0.52       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (![X22 : $i, X23 : $i]:
% 0.21/0.52         (~ (l1_struct_0 @ X22)
% 0.21/0.52          | ~ (l1_struct_0 @ X23)
% 0.21/0.52          | (r1_tsep_1 @ X23 @ X22)
% 0.21/0.52          | ~ (r1_tsep_1 @ X22 @ X23))),
% 0.21/0.52      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      ((((r1_tsep_1 @ sk_D_2 @ sk_C_1)
% 0.21/0.52         | ~ (l1_struct_0 @ sk_D_2)
% 0.21/0.52         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.52  thf('55', plain, ((l1_struct_0 @ sk_D_2)),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('56', plain, ((l1_struct_0 @ sk_C_1)),
% 0.21/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.52  thf('57', plain,
% 0.21/0.52      (((r1_tsep_1 @ sk_D_2 @ sk_C_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.21/0.52      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.21/0.52  thf('58', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i]:
% 0.21/0.52         (~ (l1_struct_0 @ X20)
% 0.21/0.52          | ~ (r1_tsep_1 @ X21 @ X20)
% 0.21/0.52          | (r1_xboole_0 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.21/0.52          | ~ (l1_struct_0 @ X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      (((~ (l1_struct_0 @ sk_D_2)
% 0.21/0.52         | (r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.52         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.52  thf('60', plain, ((l1_struct_0 @ sk_D_2)),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('61', plain, ((l1_struct_0 @ sk_C_1)),
% 0.21/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.52  thf('62', plain,
% 0.21/0.52      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.52         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.21/0.52      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.21/0.52  thf('63', plain,
% 0.21/0.52      ((((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1))
% 0.21/0.52         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['51', '62'])).
% 0.21/0.52  thf('64', plain, ((l1_struct_0 @ sk_C_1)),
% 0.21/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.52  thf('65', plain,
% 0.21/0.52      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1)))
% 0.21/0.52         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.21/0.52      inference('demod', [status(thm)], ['63', '64'])).
% 0.21/0.52  thf('66', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_C_1))
% 0.21/0.52          | (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.52  thf('67', plain,
% 0.21/0.52      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B)))
% 0.21/0.52         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.52  thf('68', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((r1_tsep_1 @ X1 @ X0)
% 0.21/0.52          | ~ (l1_struct_0 @ X1)
% 0.21/0.52          | ~ (l1_struct_0 @ X0)
% 0.21/0.52          | ~ (r1_xboole_0 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.52  thf('69', plain,
% 0.21/0.52      (((~ (l1_struct_0 @ sk_B)
% 0.21/0.52         | ~ (l1_struct_0 @ sk_D_2)
% 0.21/0.52         | (r1_tsep_1 @ sk_D_2 @ sk_B))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.52  thf('70', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.52  thf('71', plain, ((l1_struct_0 @ sk_D_2)),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('72', plain,
% 0.21/0.52      (((r1_tsep_1 @ sk_D_2 @ sk_B)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.21/0.52      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.21/0.52  thf('73', plain,
% 0.21/0.52      (![X22 : $i, X23 : $i]:
% 0.21/0.52         (~ (l1_struct_0 @ X22)
% 0.21/0.52          | ~ (l1_struct_0 @ X23)
% 0.21/0.52          | (r1_tsep_1 @ X23 @ X22)
% 0.21/0.52          | ~ (r1_tsep_1 @ X22 @ X23))),
% 0.21/0.52      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.52  thf('74', plain,
% 0.21/0.52      ((((r1_tsep_1 @ sk_B @ sk_D_2)
% 0.21/0.52         | ~ (l1_struct_0 @ sk_B)
% 0.21/0.52         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.52  thf('75', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.52  thf('76', plain, ((l1_struct_0 @ sk_D_2)),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('77', plain,
% 0.21/0.52      (((r1_tsep_1 @ sk_B @ sk_D_2)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.21/0.52      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.21/0.52  thf('78', plain,
% 0.21/0.52      ((~ (r1_tsep_1 @ sk_B @ sk_D_2)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_2)))),
% 0.21/0.52      inference('split', [status(esa)], ['48'])).
% 0.21/0.52  thf('79', plain,
% 0.21/0.52      (~ ((r1_tsep_1 @ sk_C_1 @ sk_D_2)) | ((r1_tsep_1 @ sk_B @ sk_D_2))),
% 0.21/0.52      inference('sup-', [status(thm)], ['77', '78'])).
% 0.21/0.52  thf('80', plain,
% 0.21/0.52      (((r1_tsep_1 @ sk_D_2 @ sk_B)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.21/0.52      inference('demod', [status(thm)], ['42', '45', '46'])).
% 0.21/0.52  thf('81', plain,
% 0.21/0.52      (![X22 : $i, X23 : $i]:
% 0.21/0.52         (~ (l1_struct_0 @ X22)
% 0.21/0.52          | ~ (l1_struct_0 @ X23)
% 0.21/0.52          | (r1_tsep_1 @ X23 @ X22)
% 0.21/0.52          | ~ (r1_tsep_1 @ X22 @ X23))),
% 0.21/0.52      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.52  thf('82', plain,
% 0.21/0.52      ((((r1_tsep_1 @ sk_B @ sk_D_2)
% 0.21/0.52         | ~ (l1_struct_0 @ sk_B)
% 0.21/0.52         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['80', '81'])).
% 0.21/0.52  thf('83', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.52  thf('84', plain, ((l1_struct_0 @ sk_D_2)),
% 0.21/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('85', plain,
% 0.21/0.52      (((r1_tsep_1 @ sk_B @ sk_D_2)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.21/0.52      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.21/0.52  thf('86', plain,
% 0.21/0.52      ((~ (r1_tsep_1 @ sk_B @ sk_D_2)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_2)))),
% 0.21/0.52      inference('split', [status(esa)], ['48'])).
% 0.21/0.52  thf('87', plain,
% 0.21/0.52      (~ ((r1_tsep_1 @ sk_D_2 @ sk_C_1)) | ((r1_tsep_1 @ sk_B @ sk_D_2))),
% 0.21/0.52      inference('sup-', [status(thm)], ['85', '86'])).
% 0.21/0.52  thf('88', plain,
% 0.21/0.52      (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D_2))),
% 0.21/0.52      inference('split', [status(esa)], ['48'])).
% 0.21/0.52  thf('89', plain,
% 0.21/0.52      (((r1_tsep_1 @ sk_D_2 @ sk_B)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.21/0.52      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.21/0.52  thf('90', plain,
% 0.21/0.52      ((~ (r1_tsep_1 @ sk_D_2 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)))),
% 0.21/0.52      inference('split', [status(esa)], ['48'])).
% 0.21/0.52  thf('91', plain,
% 0.21/0.52      (~ ((r1_tsep_1 @ sk_C_1 @ sk_D_2)) | ((r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['89', '90'])).
% 0.21/0.52  thf('92', plain,
% 0.21/0.52      (((r1_tsep_1 @ sk_C_1 @ sk_D_2)) | ((r1_tsep_1 @ sk_D_2 @ sk_C_1))),
% 0.21/0.52      inference('split', [status(esa)], ['1'])).
% 0.21/0.52  thf('93', plain, ($false),
% 0.21/0.52      inference('sat_resolution*', [status(thm)],
% 0.21/0.52                ['50', '79', '87', '88', '91', '92'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
