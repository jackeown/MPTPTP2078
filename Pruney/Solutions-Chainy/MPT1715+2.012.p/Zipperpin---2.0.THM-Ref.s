%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fhVFh4qq20

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:25 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 649 expanded)
%              Number of leaves         :   33 ( 206 expanded)
%              Depth                    :   18
%              Number of atoms          :  799 (8797 expanded)
%              Number of equality atoms :   11 (  30 expanded)
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

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('24',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
      = ( u1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
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

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ( r1_tarski @ ( k2_struct_0 @ X12 ) @ ( k2_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['14','15'])).

thf('29',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['27','28','33'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('35',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_xboole_0 @ X3 @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( k4_xboole_0 @ X0 @ ( k2_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['24','36'])).

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
      ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tsep_1 @ X0 @ X1 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ( r1_tsep_1 @ X0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['37','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['31','32'])).

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
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['42','45','46'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_struct_0 @ X22 )
      | ~ ( l1_struct_0 @ X23 )
      | ( r1_tsep_1 @ X23 @ X22 )
      | ~ ( r1_tsep_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('49',plain,
    ( ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('51',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['43','44'])).

thf('52',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
    | ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('57',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['1'])).

thf('58',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_struct_0 @ X22 )
      | ~ ( l1_struct_0 @ X23 )
      | ( r1_tsep_1 @ X23 @ X22 )
      | ~ ( r1_tsep_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('59',plain,
    ( ( ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_2 )
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
    ( ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( r1_tsep_1 @ X21 @ X20 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('64',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('66',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('67',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['56','67'])).

thf('69',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('70',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('72',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
      = ( u1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( k4_xboole_0 @ X0 @ ( k2_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('74',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ( r1_tsep_1 @ X0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('76',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_tsep_1 @ sk_B @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['43','44'])).

thf('78',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('79',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['53'])).

thf('81',plain,
    ( ~ ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['42','45','46'])).

thf('83',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['53'])).

thf('84',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
    | ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['53'])).

thf('86',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('87',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_struct_0 @ X22 )
      | ~ ( l1_struct_0 @ X23 )
      | ( r1_tsep_1 @ X23 @ X22 )
      | ~ ( r1_tsep_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('88',plain,
    ( ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('90',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['43','44'])).

thf('91',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['53'])).

thf('93',plain,
    ( ~ ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['1'])).

thf('95',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['55','81','84','85','93','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fhVFh4qq20
% 0.11/0.33  % Computer   : n024.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 16:29:06 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 0.18/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.49  % Solved by: fo/fo7.sh
% 0.18/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.49  % done 100 iterations in 0.040s
% 0.18/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.49  % SZS output start Refutation
% 0.18/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.18/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.18/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.18/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.18/0.49  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.18/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.49  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.18/0.49  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.18/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.18/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.18/0.49  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.18/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.18/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.18/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.18/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.18/0.49  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.18/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.18/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.18/0.49  thf(d3_struct_0, axiom,
% 0.18/0.49    (![A:$i]:
% 0.18/0.49     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.18/0.49  thf('0', plain,
% 0.18/0.49      (![X6 : $i]:
% 0.18/0.49         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.18/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.18/0.49  thf(t24_tmap_1, conjecture,
% 0.18/0.49    (![A:$i]:
% 0.18/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.18/0.49       ( ![B:$i]:
% 0.18/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.18/0.49           ( ![C:$i]:
% 0.18/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.18/0.49               ( ![D:$i]:
% 0.18/0.49                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.18/0.49                   ( ( m1_pre_topc @ B @ C ) =>
% 0.18/0.49                     ( ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.18/0.49                         ( ~( r1_tsep_1 @ D @ C ) ) ) | 
% 0.18/0.49                       ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.18/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.49    (~( ![A:$i]:
% 0.18/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.18/0.49            ( l1_pre_topc @ A ) ) =>
% 0.18/0.49          ( ![B:$i]:
% 0.18/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.18/0.49              ( ![C:$i]:
% 0.18/0.49                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.18/0.49                  ( ![D:$i]:
% 0.18/0.49                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.18/0.49                      ( ( m1_pre_topc @ B @ C ) =>
% 0.18/0.49                        ( ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.18/0.49                            ( ~( r1_tsep_1 @ D @ C ) ) ) | 
% 0.18/0.49                          ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) ) ) ) ) ) ) ) ) ) )),
% 0.18/0.49    inference('cnf.neg', [status(esa)], [t24_tmap_1])).
% 0.18/0.49  thf('1', plain,
% 0.18/0.49      (((r1_tsep_1 @ sk_C_1 @ sk_D_2) | (r1_tsep_1 @ sk_D_2 @ sk_C_1))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('2', plain,
% 0.18/0.49      (((r1_tsep_1 @ sk_D_2 @ sk_C_1)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.18/0.49      inference('split', [status(esa)], ['1'])).
% 0.18/0.49  thf(d3_tsep_1, axiom,
% 0.18/0.49    (![A:$i]:
% 0.18/0.49     ( ( l1_struct_0 @ A ) =>
% 0.18/0.49       ( ![B:$i]:
% 0.18/0.49         ( ( l1_struct_0 @ B ) =>
% 0.18/0.49           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.18/0.49             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.18/0.49  thf('3', plain,
% 0.18/0.49      (![X20 : $i, X21 : $i]:
% 0.18/0.49         (~ (l1_struct_0 @ X20)
% 0.18/0.49          | ~ (r1_tsep_1 @ X21 @ X20)
% 0.18/0.49          | (r1_xboole_0 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.18/0.49          | ~ (l1_struct_0 @ X21))),
% 0.18/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.18/0.49  thf('4', plain,
% 0.18/0.49      (((~ (l1_struct_0 @ sk_D_2)
% 0.18/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 0.18/0.49         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.18/0.49  thf('5', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf(dt_m1_pre_topc, axiom,
% 0.18/0.49    (![A:$i]:
% 0.18/0.49     ( ( l1_pre_topc @ A ) =>
% 0.18/0.49       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.18/0.49  thf('6', plain,
% 0.18/0.49      (![X18 : $i, X19 : $i]:
% 0.18/0.49         (~ (m1_pre_topc @ X18 @ X19)
% 0.18/0.49          | (l1_pre_topc @ X18)
% 0.18/0.49          | ~ (l1_pre_topc @ X19))),
% 0.18/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.18/0.49  thf('7', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D_2))),
% 0.18/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.18/0.49  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('9', plain, ((l1_pre_topc @ sk_D_2)),
% 0.18/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.18/0.49  thf(dt_l1_pre_topc, axiom,
% 0.18/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.18/0.49  thf('10', plain,
% 0.18/0.49      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.18/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.18/0.49  thf('11', plain, ((l1_struct_0 @ sk_D_2)),
% 0.18/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.18/0.49  thf('12', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('13', plain,
% 0.18/0.49      (![X18 : $i, X19 : $i]:
% 0.18/0.49         (~ (m1_pre_topc @ X18 @ X19)
% 0.18/0.49          | (l1_pre_topc @ X18)
% 0.18/0.49          | ~ (l1_pre_topc @ X19))),
% 0.18/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.18/0.49  thf('14', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.18/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.18/0.49  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('16', plain, ((l1_pre_topc @ sk_C_1)),
% 0.18/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.18/0.49  thf('17', plain,
% 0.18/0.49      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.18/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.18/0.49  thf('18', plain, ((l1_struct_0 @ sk_C_1)),
% 0.18/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.18/0.49  thf('19', plain,
% 0.18/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 0.18/0.49         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.18/0.49      inference('demod', [status(thm)], ['4', '11', '18'])).
% 0.18/0.49  thf('20', plain,
% 0.18/0.49      ((((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1))
% 0.18/0.49         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.18/0.49      inference('sup+', [status(thm)], ['0', '19'])).
% 0.18/0.49  thf('21', plain, ((l1_struct_0 @ sk_C_1)),
% 0.18/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.18/0.49  thf('22', plain,
% 0.18/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1)))
% 0.18/0.49         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.18/0.49      inference('demod', [status(thm)], ['20', '21'])).
% 0.18/0.49  thf(t83_xboole_1, axiom,
% 0.18/0.49    (![A:$i,B:$i]:
% 0.18/0.49     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.18/0.49  thf('23', plain,
% 0.18/0.49      (![X0 : $i, X1 : $i]:
% 0.18/0.49         (((k4_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.18/0.49      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.18/0.49  thf('24', plain,
% 0.18/0.49      ((((k4_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1))
% 0.18/0.49          = (u1_struct_0 @ sk_D_2)))
% 0.18/0.49         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.18/0.49  thf('25', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf(d9_pre_topc, axiom,
% 0.18/0.49    (![A:$i]:
% 0.18/0.49     ( ( l1_pre_topc @ A ) =>
% 0.18/0.49       ( ![B:$i]:
% 0.18/0.49         ( ( l1_pre_topc @ B ) =>
% 0.18/0.49           ( ( m1_pre_topc @ B @ A ) <=>
% 0.18/0.49             ( ( ![C:$i]:
% 0.18/0.49                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.18/0.49                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.18/0.49                     ( ?[D:$i]:
% 0.18/0.49                       ( ( m1_subset_1 @
% 0.18/0.49                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.18/0.49                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.18/0.49                         ( ( C ) =
% 0.18/0.49                           ( k9_subset_1 @
% 0.18/0.49                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 0.18/0.49               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 0.18/0.49  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.18/0.49  thf(zf_stmt_2, axiom,
% 0.18/0.49    (![D:$i,C:$i,B:$i,A:$i]:
% 0.18/0.49     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.18/0.49       ( ( ( C ) =
% 0.18/0.49           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 0.18/0.49         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.18/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.18/0.49  thf(zf_stmt_3, axiom,
% 0.18/0.49    (![A:$i]:
% 0.18/0.49     ( ( l1_pre_topc @ A ) =>
% 0.18/0.49       ( ![B:$i]:
% 0.18/0.49         ( ( l1_pre_topc @ B ) =>
% 0.18/0.49           ( ( m1_pre_topc @ B @ A ) <=>
% 0.18/0.49             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 0.18/0.49               ( ![C:$i]:
% 0.18/0.49                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.18/0.49                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.18/0.49                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.18/0.49  thf('26', plain,
% 0.18/0.49      (![X12 : $i, X13 : $i]:
% 0.18/0.49         (~ (l1_pre_topc @ X12)
% 0.18/0.49          | ~ (m1_pre_topc @ X12 @ X13)
% 0.18/0.49          | (r1_tarski @ (k2_struct_0 @ X12) @ (k2_struct_0 @ X13))
% 0.18/0.49          | ~ (l1_pre_topc @ X13))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.18/0.49  thf('27', plain,
% 0.18/0.49      ((~ (l1_pre_topc @ sk_C_1)
% 0.18/0.49        | (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))
% 0.18/0.49        | ~ (l1_pre_topc @ sk_B))),
% 0.18/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.18/0.49  thf('28', plain, ((l1_pre_topc @ sk_C_1)),
% 0.18/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.18/0.49  thf('29', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('30', plain,
% 0.18/0.49      (![X18 : $i, X19 : $i]:
% 0.18/0.49         (~ (m1_pre_topc @ X18 @ X19)
% 0.18/0.49          | (l1_pre_topc @ X18)
% 0.18/0.49          | ~ (l1_pre_topc @ X19))),
% 0.18/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.18/0.49  thf('31', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.18/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.18/0.49  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('33', plain, ((l1_pre_topc @ sk_B)),
% 0.18/0.49      inference('demod', [status(thm)], ['31', '32'])).
% 0.18/0.49  thf('34', plain,
% 0.18/0.49      ((r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))),
% 0.18/0.49      inference('demod', [status(thm)], ['27', '28', '33'])).
% 0.18/0.49  thf(t85_xboole_1, axiom,
% 0.18/0.49    (![A:$i,B:$i,C:$i]:
% 0.18/0.49     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.18/0.49  thf('35', plain,
% 0.18/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.18/0.49         (~ (r1_tarski @ X3 @ X4)
% 0.18/0.49          | (r1_xboole_0 @ X3 @ (k4_xboole_0 @ X5 @ X4)))),
% 0.18/0.49      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.18/0.49  thf('36', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         (r1_xboole_0 @ (k2_struct_0 @ sk_B) @ 
% 0.18/0.49          (k4_xboole_0 @ X0 @ (k2_struct_0 @ sk_C_1)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.18/0.49  thf('37', plain,
% 0.18/0.49      (((r1_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)))
% 0.18/0.49         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.18/0.49      inference('sup+', [status(thm)], ['24', '36'])).
% 0.18/0.49  thf('38', plain,
% 0.18/0.49      (![X6 : $i]:
% 0.18/0.49         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.18/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.18/0.49  thf('39', plain,
% 0.18/0.49      (![X20 : $i, X21 : $i]:
% 0.18/0.49         (~ (l1_struct_0 @ X20)
% 0.18/0.49          | ~ (r1_xboole_0 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.18/0.49          | (r1_tsep_1 @ X21 @ X20)
% 0.18/0.49          | ~ (l1_struct_0 @ X21))),
% 0.18/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.18/0.49  thf('40', plain,
% 0.18/0.49      (![X0 : $i, X1 : $i]:
% 0.18/0.49         (~ (r1_xboole_0 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.18/0.49          | ~ (l1_struct_0 @ X0)
% 0.18/0.49          | ~ (l1_struct_0 @ X0)
% 0.18/0.49          | (r1_tsep_1 @ X0 @ X1)
% 0.18/0.49          | ~ (l1_struct_0 @ X1))),
% 0.18/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.18/0.49  thf('41', plain,
% 0.18/0.49      (![X0 : $i, X1 : $i]:
% 0.18/0.49         (~ (l1_struct_0 @ X1)
% 0.18/0.49          | (r1_tsep_1 @ X0 @ X1)
% 0.18/0.49          | ~ (l1_struct_0 @ X0)
% 0.18/0.49          | ~ (r1_xboole_0 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1)))),
% 0.18/0.49      inference('simplify', [status(thm)], ['40'])).
% 0.18/0.49  thf('42', plain,
% 0.18/0.49      (((~ (l1_struct_0 @ sk_B)
% 0.18/0.49         | (r1_tsep_1 @ sk_B @ sk_D_2)
% 0.18/0.49         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['37', '41'])).
% 0.18/0.49  thf('43', plain, ((l1_pre_topc @ sk_B)),
% 0.18/0.49      inference('demod', [status(thm)], ['31', '32'])).
% 0.18/0.49  thf('44', plain,
% 0.18/0.49      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.18/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.18/0.49  thf('45', plain, ((l1_struct_0 @ sk_B)),
% 0.18/0.49      inference('sup-', [status(thm)], ['43', '44'])).
% 0.18/0.49  thf('46', plain, ((l1_struct_0 @ sk_D_2)),
% 0.18/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.18/0.49  thf('47', plain,
% 0.18/0.49      (((r1_tsep_1 @ sk_B @ sk_D_2)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.18/0.49      inference('demod', [status(thm)], ['42', '45', '46'])).
% 0.18/0.49  thf(symmetry_r1_tsep_1, axiom,
% 0.18/0.49    (![A:$i,B:$i]:
% 0.18/0.49     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.18/0.49       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.18/0.49  thf('48', plain,
% 0.18/0.49      (![X22 : $i, X23 : $i]:
% 0.18/0.49         (~ (l1_struct_0 @ X22)
% 0.18/0.49          | ~ (l1_struct_0 @ X23)
% 0.18/0.49          | (r1_tsep_1 @ X23 @ X22)
% 0.18/0.49          | ~ (r1_tsep_1 @ X22 @ X23))),
% 0.18/0.49      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.18/0.49  thf('49', plain,
% 0.18/0.49      ((((r1_tsep_1 @ sk_D_2 @ sk_B)
% 0.18/0.49         | ~ (l1_struct_0 @ sk_D_2)
% 0.18/0.49         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.18/0.49  thf('50', plain, ((l1_struct_0 @ sk_D_2)),
% 0.18/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.18/0.49  thf('51', plain, ((l1_struct_0 @ sk_B)),
% 0.18/0.49      inference('sup-', [status(thm)], ['43', '44'])).
% 0.18/0.49  thf('52', plain,
% 0.18/0.49      (((r1_tsep_1 @ sk_D_2 @ sk_B)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.18/0.49      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.18/0.49  thf('53', plain,
% 0.18/0.49      ((~ (r1_tsep_1 @ sk_B @ sk_D_2) | ~ (r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.18/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.49  thf('54', plain,
% 0.18/0.49      ((~ (r1_tsep_1 @ sk_D_2 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)))),
% 0.18/0.49      inference('split', [status(esa)], ['53'])).
% 0.18/0.49  thf('55', plain,
% 0.18/0.49      (~ ((r1_tsep_1 @ sk_D_2 @ sk_C_1)) | ((r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.18/0.49      inference('sup-', [status(thm)], ['52', '54'])).
% 0.18/0.49  thf('56', plain,
% 0.18/0.49      (![X6 : $i]:
% 0.18/0.49         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.18/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.18/0.49  thf('57', plain,
% 0.18/0.49      (((r1_tsep_1 @ sk_C_1 @ sk_D_2)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.18/0.49      inference('split', [status(esa)], ['1'])).
% 0.18/0.49  thf('58', plain,
% 0.18/0.49      (![X22 : $i, X23 : $i]:
% 0.18/0.49         (~ (l1_struct_0 @ X22)
% 0.18/0.49          | ~ (l1_struct_0 @ X23)
% 0.18/0.49          | (r1_tsep_1 @ X23 @ X22)
% 0.18/0.49          | ~ (r1_tsep_1 @ X22 @ X23))),
% 0.18/0.49      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.18/0.49  thf('59', plain,
% 0.18/0.49      ((((r1_tsep_1 @ sk_D_2 @ sk_C_1)
% 0.18/0.49         | ~ (l1_struct_0 @ sk_D_2)
% 0.18/0.49         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['57', '58'])).
% 0.18/0.49  thf('60', plain, ((l1_struct_0 @ sk_D_2)),
% 0.18/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.18/0.49  thf('61', plain, ((l1_struct_0 @ sk_C_1)),
% 0.18/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.18/0.49  thf('62', plain,
% 0.18/0.49      (((r1_tsep_1 @ sk_D_2 @ sk_C_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.18/0.49      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.18/0.49  thf('63', plain,
% 0.18/0.49      (![X20 : $i, X21 : $i]:
% 0.18/0.49         (~ (l1_struct_0 @ X20)
% 0.18/0.49          | ~ (r1_tsep_1 @ X21 @ X20)
% 0.18/0.49          | (r1_xboole_0 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.18/0.49          | ~ (l1_struct_0 @ X21))),
% 0.18/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.18/0.49  thf('64', plain,
% 0.18/0.49      (((~ (l1_struct_0 @ sk_D_2)
% 0.18/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 0.18/0.49         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['62', '63'])).
% 0.18/0.49  thf('65', plain, ((l1_struct_0 @ sk_D_2)),
% 0.18/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.18/0.49  thf('66', plain, ((l1_struct_0 @ sk_C_1)),
% 0.18/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.18/0.49  thf('67', plain,
% 0.18/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 0.18/0.49         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.18/0.49      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.18/0.49  thf('68', plain,
% 0.18/0.49      ((((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1))
% 0.18/0.49         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.18/0.49      inference('sup+', [status(thm)], ['56', '67'])).
% 0.18/0.49  thf('69', plain, ((l1_struct_0 @ sk_C_1)),
% 0.18/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.18/0.49  thf('70', plain,
% 0.18/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1)))
% 0.18/0.49         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.18/0.49      inference('demod', [status(thm)], ['68', '69'])).
% 0.18/0.49  thf('71', plain,
% 0.18/0.49      (![X0 : $i, X1 : $i]:
% 0.18/0.49         (((k4_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.18/0.49      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.18/0.49  thf('72', plain,
% 0.18/0.49      ((((k4_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1))
% 0.18/0.49          = (u1_struct_0 @ sk_D_2)))
% 0.18/0.49         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['70', '71'])).
% 0.18/0.49  thf('73', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         (r1_xboole_0 @ (k2_struct_0 @ sk_B) @ 
% 0.18/0.49          (k4_xboole_0 @ X0 @ (k2_struct_0 @ sk_C_1)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.18/0.49  thf('74', plain,
% 0.18/0.49      (((r1_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_D_2)))
% 0.18/0.49         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.18/0.49      inference('sup+', [status(thm)], ['72', '73'])).
% 0.18/0.49  thf('75', plain,
% 0.18/0.49      (![X0 : $i, X1 : $i]:
% 0.18/0.49         (~ (l1_struct_0 @ X1)
% 0.18/0.49          | (r1_tsep_1 @ X0 @ X1)
% 0.18/0.49          | ~ (l1_struct_0 @ X0)
% 0.18/0.49          | ~ (r1_xboole_0 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1)))),
% 0.18/0.49      inference('simplify', [status(thm)], ['40'])).
% 0.18/0.49  thf('76', plain,
% 0.18/0.49      (((~ (l1_struct_0 @ sk_B)
% 0.18/0.49         | (r1_tsep_1 @ sk_B @ sk_D_2)
% 0.18/0.49         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['74', '75'])).
% 0.18/0.49  thf('77', plain, ((l1_struct_0 @ sk_B)),
% 0.18/0.49      inference('sup-', [status(thm)], ['43', '44'])).
% 0.18/0.49  thf('78', plain, ((l1_struct_0 @ sk_D_2)),
% 0.18/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.18/0.49  thf('79', plain,
% 0.18/0.49      (((r1_tsep_1 @ sk_B @ sk_D_2)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.18/0.49      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.18/0.49  thf('80', plain,
% 0.18/0.49      ((~ (r1_tsep_1 @ sk_B @ sk_D_2)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_2)))),
% 0.18/0.49      inference('split', [status(esa)], ['53'])).
% 0.18/0.49  thf('81', plain,
% 0.18/0.49      (~ ((r1_tsep_1 @ sk_C_1 @ sk_D_2)) | ((r1_tsep_1 @ sk_B @ sk_D_2))),
% 0.18/0.49      inference('sup-', [status(thm)], ['79', '80'])).
% 0.18/0.49  thf('82', plain,
% 0.18/0.49      (((r1_tsep_1 @ sk_B @ sk_D_2)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.18/0.49      inference('demod', [status(thm)], ['42', '45', '46'])).
% 0.18/0.49  thf('83', plain,
% 0.18/0.49      ((~ (r1_tsep_1 @ sk_B @ sk_D_2)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_2)))),
% 0.18/0.49      inference('split', [status(esa)], ['53'])).
% 0.18/0.49  thf('84', plain,
% 0.18/0.49      (~ ((r1_tsep_1 @ sk_D_2 @ sk_C_1)) | ((r1_tsep_1 @ sk_B @ sk_D_2))),
% 0.18/0.49      inference('sup-', [status(thm)], ['82', '83'])).
% 0.18/0.49  thf('85', plain,
% 0.18/0.49      (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D_2))),
% 0.18/0.49      inference('split', [status(esa)], ['53'])).
% 0.18/0.49  thf('86', plain,
% 0.18/0.49      (((r1_tsep_1 @ sk_B @ sk_D_2)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.18/0.49      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.18/0.49  thf('87', plain,
% 0.18/0.49      (![X22 : $i, X23 : $i]:
% 0.18/0.49         (~ (l1_struct_0 @ X22)
% 0.18/0.49          | ~ (l1_struct_0 @ X23)
% 0.18/0.49          | (r1_tsep_1 @ X23 @ X22)
% 0.18/0.49          | ~ (r1_tsep_1 @ X22 @ X23))),
% 0.18/0.49      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.18/0.49  thf('88', plain,
% 0.18/0.49      ((((r1_tsep_1 @ sk_D_2 @ sk_B)
% 0.18/0.49         | ~ (l1_struct_0 @ sk_D_2)
% 0.18/0.49         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['86', '87'])).
% 0.18/0.49  thf('89', plain, ((l1_struct_0 @ sk_D_2)),
% 0.18/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.18/0.49  thf('90', plain, ((l1_struct_0 @ sk_B)),
% 0.18/0.49      inference('sup-', [status(thm)], ['43', '44'])).
% 0.18/0.49  thf('91', plain,
% 0.18/0.49      (((r1_tsep_1 @ sk_D_2 @ sk_B)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.18/0.49      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.18/0.49  thf('92', plain,
% 0.18/0.49      ((~ (r1_tsep_1 @ sk_D_2 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)))),
% 0.18/0.49      inference('split', [status(esa)], ['53'])).
% 0.18/0.49  thf('93', plain,
% 0.18/0.49      (~ ((r1_tsep_1 @ sk_C_1 @ sk_D_2)) | ((r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.18/0.49      inference('sup-', [status(thm)], ['91', '92'])).
% 0.18/0.49  thf('94', plain,
% 0.18/0.49      (((r1_tsep_1 @ sk_C_1 @ sk_D_2)) | ((r1_tsep_1 @ sk_D_2 @ sk_C_1))),
% 0.18/0.49      inference('split', [status(esa)], ['1'])).
% 0.18/0.49  thf('95', plain, ($false),
% 0.18/0.49      inference('sat_resolution*', [status(thm)],
% 0.18/0.49                ['55', '81', '84', '85', '93', '94'])).
% 0.18/0.49  
% 0.18/0.49  % SZS output end Refutation
% 0.18/0.49  
% 0.18/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
