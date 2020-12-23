%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.T2zkLZLt2N

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 986 expanded)
%              Number of leaves         :   33 ( 302 expanded)
%              Depth                    :   23
%              Number of atoms          :  880 (13503 expanded)
%              Number of equality atoms :   12 (  52 expanded)
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

thf(t23_tmap_1,conjecture,(
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
                   => ( ( ( r1_tsep_1 @ B @ D )
                        & ( r1_tsep_1 @ D @ B ) )
                      | ( ~ ( r1_tsep_1 @ C @ D )
                        & ~ ( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) )).

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
                     => ( ( ( r1_tsep_1 @ B @ D )
                          & ( r1_tsep_1 @ D @ B ) )
                        | ( ~ ( r1_tsep_1 @ C @ D )
                          & ~ ( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_tmap_1])).

thf('0',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
    | ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('4',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['4'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_struct_0 @ X22 )
      | ~ ( l1_struct_0 @ X23 )
      | ( r1_tsep_1 @ X23 @ X22 )
      | ~ ( r1_tsep_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('7',plain,
    ( ( ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['10','11'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('13',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('14',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('21',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['7','14','21'])).

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
    ( ( ~ ( l1_struct_0 @ sk_D_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('26',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('27',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['3','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('30',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['2','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('33',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('35',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('36',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( r1_tsep_1 @ X21 @ X20 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('37',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('39',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('40',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['34','40'])).

thf('42',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('43',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
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

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_pre_topc @ X12 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ( r1_tarski @ ( k2_struct_0 @ X12 ) @ ( k2_struct_0 @ X13 ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('48',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_pre_topc @ X18 @ X19 )
      | ( l1_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('50',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['46','47','52'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('55',plain,
    ( ( k2_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('56',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['43','57'])).

thf('59',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('60',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ( r1_tsep_1 @ X21 @ X20 )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( u1_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r1_tsep_1 @ X1 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tsep_1 @ X1 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_2 )
      | ( r1_tsep_1 @ sk_D_2 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['58','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['50','51'])).

thf('65',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('66',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('68',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['63','66','67'])).

thf('69',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_struct_0 @ X22 )
      | ~ ( l1_struct_0 @ X23 )
      | ( r1_tsep_1 @ X23 @ X22 )
      | ~ ( r1_tsep_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('70',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['64','65'])).

thf('72',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('73',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('75',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
    | ~ ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['63','66','67'])).

thf('77',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('78',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('80',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('81',plain,(
    r1_tsep_1 @ sk_C_1 @ sk_D_2 ),
    inference('sat_resolution*',[status(thm)],['75','78','79','80'])).

thf('82',plain,(
    r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['33','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_C_1 ) )
      | ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('84',plain,(
    r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('86',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('87',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_struct_0 @ X20 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X20 ) )
      | ( r1_tsep_1 @ X21 @ X20 )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tsep_1 @ X0 @ X1 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ( r1_tsep_1 @ X0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r1_tsep_1 @ X1 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tsep_1 @ X1 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['84','91'])).

thf('93',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['64','65'])).

thf('94',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('95',plain,(
    r1_tsep_1 @ sk_D_2 @ sk_B ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_struct_0 @ X22 )
      | ~ ( l1_struct_0 @ X23 )
      | ( r1_tsep_1 @ X23 @ X22 )
      | ~ ( r1_tsep_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('97',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
    | ~ ( l1_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['64','65'])).

thf('99',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('100',plain,(
    r1_tsep_1 @ sk_B @ sk_D_2 ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,
    ( $false
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(demod,[status(thm)],['1','100'])).

thf('102',plain,(
    r1_tsep_1 @ sk_D_2 @ sk_B ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('103',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('104',plain,(
    r1_tsep_1 @ sk_D_2 @ sk_B ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
    | ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('106',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference('sat_resolution*',[status(thm)],['104','105'])).

thf('107',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['101','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.T2zkLZLt2N
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:54:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 100 iterations in 0.052s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.51  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.22/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.51  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.22/0.51  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.22/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.51  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.22/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.51  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.51  thf(t23_tmap_1, conjecture,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.22/0.51           ( ![C:$i]:
% 0.22/0.51             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.51               ( ![D:$i]:
% 0.22/0.51                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.51                   ( ( m1_pre_topc @ B @ C ) =>
% 0.22/0.51                     ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.22/0.51                       ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.22/0.51                         ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i]:
% 0.22/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.51            ( l1_pre_topc @ A ) ) =>
% 0.22/0.51          ( ![B:$i]:
% 0.22/0.51            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.22/0.51              ( ![C:$i]:
% 0.22/0.51                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.51                  ( ![D:$i]:
% 0.22/0.51                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.51                      ( ( m1_pre_topc @ B @ C ) =>
% 0.22/0.51                        ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.22/0.51                          ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.22/0.51                            ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t23_tmap_1])).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      ((~ (r1_tsep_1 @ sk_B @ sk_D_2) | ~ (r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      ((~ (r1_tsep_1 @ sk_B @ sk_D_2)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_2)))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf(d3_struct_0, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X6 : $i]:
% 0.22/0.51         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (![X6 : $i]:
% 0.22/0.51         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      (((r1_tsep_1 @ sk_C_1 @ sk_D_2) | (r1_tsep_1 @ sk_D_2 @ sk_C_1))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (((r1_tsep_1 @ sk_C_1 @ sk_D_2)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.22/0.51      inference('split', [status(esa)], ['4'])).
% 0.22/0.51  thf(symmetry_r1_tsep_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.22/0.51       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      (![X22 : $i, X23 : $i]:
% 0.22/0.51         (~ (l1_struct_0 @ X22)
% 0.22/0.51          | ~ (l1_struct_0 @ X23)
% 0.22/0.51          | (r1_tsep_1 @ X23 @ X22)
% 0.22/0.51          | ~ (r1_tsep_1 @ X22 @ X23))),
% 0.22/0.51      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      ((((r1_tsep_1 @ sk_D_2 @ sk_C_1)
% 0.22/0.51         | ~ (l1_struct_0 @ sk_D_2)
% 0.22/0.51         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.51  thf('8', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(dt_m1_pre_topc, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (![X18 : $i, X19 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X18 @ X19)
% 0.22/0.51          | (l1_pre_topc @ X18)
% 0.22/0.51          | ~ (l1_pre_topc @ X19))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.51  thf('10', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D_2))),
% 0.22/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.51  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('12', plain, ((l1_pre_topc @ sk_D_2)),
% 0.22/0.51      inference('demod', [status(thm)], ['10', '11'])).
% 0.22/0.51  thf(dt_l1_pre_topc, axiom,
% 0.22/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.51  thf('14', plain, ((l1_struct_0 @ sk_D_2)),
% 0.22/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.51  thf('15', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      (![X18 : $i, X19 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X18 @ X19)
% 0.22/0.51          | (l1_pre_topc @ X18)
% 0.22/0.51          | ~ (l1_pre_topc @ X19))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.51  thf('17', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.22/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.51  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('19', plain, ((l1_pre_topc @ sk_C_1)),
% 0.22/0.51      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.51  thf('21', plain, ((l1_struct_0 @ sk_C_1)),
% 0.22/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (((r1_tsep_1 @ sk_D_2 @ sk_C_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.22/0.51      inference('demod', [status(thm)], ['7', '14', '21'])).
% 0.22/0.51  thf(d3_tsep_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_struct_0 @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( l1_struct_0 @ B ) =>
% 0.22/0.51           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.22/0.51             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      (![X20 : $i, X21 : $i]:
% 0.22/0.51         (~ (l1_struct_0 @ X20)
% 0.22/0.51          | ~ (r1_tsep_1 @ X21 @ X20)
% 0.22/0.51          | (r1_xboole_0 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.22/0.51          | ~ (l1_struct_0 @ X21))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (((~ (l1_struct_0 @ sk_D_2)
% 0.22/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 0.22/0.51         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.51  thf('25', plain, ((l1_struct_0 @ sk_D_2)),
% 0.22/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.51  thf('26', plain, ((l1_struct_0 @ sk_C_1)),
% 0.22/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.51  thf('27', plain,
% 0.22/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.22/0.51      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.22/0.51  thf('28', plain,
% 0.22/0.51      ((((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 0.22/0.51         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['3', '27'])).
% 0.22/0.51  thf('29', plain, ((l1_struct_0 @ sk_D_2)),
% 0.22/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.51  thf('30', plain,
% 0.22/0.51      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.22/0.51      inference('demod', [status(thm)], ['28', '29'])).
% 0.22/0.51  thf('31', plain,
% 0.22/0.51      ((((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1))
% 0.22/0.51         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['2', '30'])).
% 0.22/0.51  thf('32', plain, ((l1_struct_0 @ sk_C_1)),
% 0.22/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.51  thf('33', plain,
% 0.22/0.51      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1)))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.22/0.51      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.51  thf('34', plain,
% 0.22/0.51      (![X6 : $i]:
% 0.22/0.51         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.51  thf('35', plain,
% 0.22/0.51      (((r1_tsep_1 @ sk_D_2 @ sk_C_1)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.22/0.51      inference('split', [status(esa)], ['4'])).
% 0.22/0.51  thf('36', plain,
% 0.22/0.51      (![X20 : $i, X21 : $i]:
% 0.22/0.51         (~ (l1_struct_0 @ X20)
% 0.22/0.51          | ~ (r1_tsep_1 @ X21 @ X20)
% 0.22/0.51          | (r1_xboole_0 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.22/0.51          | ~ (l1_struct_0 @ X21))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.22/0.51  thf('37', plain,
% 0.22/0.51      (((~ (l1_struct_0 @ sk_D_2)
% 0.22/0.51         | (r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 0.22/0.51         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.51  thf('38', plain, ((l1_struct_0 @ sk_D_2)),
% 0.22/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.51  thf('39', plain, ((l1_struct_0 @ sk_C_1)),
% 0.22/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.51  thf('40', plain,
% 0.22/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.22/0.51      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.22/0.51  thf('41', plain,
% 0.22/0.51      ((((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1))
% 0.22/0.51         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['34', '40'])).
% 0.22/0.51  thf('42', plain, ((l1_struct_0 @ sk_C_1)),
% 0.22/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.51  thf('43', plain,
% 0.22/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1)))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.22/0.51      inference('demod', [status(thm)], ['41', '42'])).
% 0.22/0.51  thf('44', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(d9_pre_topc, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( l1_pre_topc @ B ) =>
% 0.22/0.51           ( ( m1_pre_topc @ B @ A ) <=>
% 0.22/0.51             ( ( ![C:$i]:
% 0.22/0.51                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.51                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.22/0.51                     ( ?[D:$i]:
% 0.22/0.51                       ( ( m1_subset_1 @
% 0.22/0.51                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.22/0.51                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.22/0.51                         ( ( C ) =
% 0.22/0.51                           ( k9_subset_1 @
% 0.22/0.51                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 0.22/0.51               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.22/0.51  thf(zf_stmt_2, axiom,
% 0.22/0.51    (![D:$i,C:$i,B:$i,A:$i]:
% 0.22/0.51     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.22/0.51       ( ( ( C ) =
% 0.22/0.51           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 0.22/0.51         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.22/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_3, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( l1_pre_topc @ A ) =>
% 0.22/0.51       ( ![B:$i]:
% 0.22/0.51         ( ( l1_pre_topc @ B ) =>
% 0.22/0.51           ( ( m1_pre_topc @ B @ A ) <=>
% 0.22/0.51             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 0.22/0.51               ( ![C:$i]:
% 0.22/0.51                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.51                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.22/0.51                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.51  thf('45', plain,
% 0.22/0.51      (![X12 : $i, X13 : $i]:
% 0.22/0.51         (~ (l1_pre_topc @ X12)
% 0.22/0.51          | ~ (m1_pre_topc @ X12 @ X13)
% 0.22/0.51          | (r1_tarski @ (k2_struct_0 @ X12) @ (k2_struct_0 @ X13))
% 0.22/0.51          | ~ (l1_pre_topc @ X13))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.51  thf('46', plain,
% 0.22/0.51      ((~ (l1_pre_topc @ sk_C_1)
% 0.22/0.51        | (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))
% 0.22/0.51        | ~ (l1_pre_topc @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.51  thf('47', plain, ((l1_pre_topc @ sk_C_1)),
% 0.22/0.51      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.51  thf('48', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('49', plain,
% 0.22/0.51      (![X18 : $i, X19 : $i]:
% 0.22/0.51         (~ (m1_pre_topc @ X18 @ X19)
% 0.22/0.51          | (l1_pre_topc @ X18)
% 0.22/0.51          | ~ (l1_pre_topc @ X19))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.51  thf('50', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.51  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('52', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('demod', [status(thm)], ['50', '51'])).
% 0.22/0.51  thf('53', plain,
% 0.22/0.51      ((r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))),
% 0.22/0.51      inference('demod', [status(thm)], ['46', '47', '52'])).
% 0.22/0.51  thf(t12_xboole_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.22/0.51  thf('54', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.22/0.51      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.22/0.51  thf('55', plain,
% 0.22/0.51      (((k2_xboole_0 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))
% 0.22/0.51         = (k2_struct_0 @ sk_C_1))),
% 0.22/0.51      inference('sup-', [status(thm)], ['53', '54'])).
% 0.22/0.51  thf(t70_xboole_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.22/0.51            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.22/0.51       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.22/0.51            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.22/0.51  thf('56', plain,
% 0.22/0.51      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.22/0.51         ((r1_xboole_0 @ X2 @ X3)
% 0.22/0.51          | ~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X3 @ X5)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.22/0.51  thf('57', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_C_1))
% 0.22/0.51          | (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_B)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['55', '56'])).
% 0.22/0.51  thf('58', plain,
% 0.22/0.51      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B)))
% 0.22/0.51         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['43', '57'])).
% 0.22/0.51  thf('59', plain,
% 0.22/0.51      (![X6 : $i]:
% 0.22/0.51         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.51  thf('60', plain,
% 0.22/0.51      (![X20 : $i, X21 : $i]:
% 0.22/0.51         (~ (l1_struct_0 @ X20)
% 0.22/0.51          | ~ (r1_xboole_0 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.22/0.51          | (r1_tsep_1 @ X21 @ X20)
% 0.22/0.51          | ~ (l1_struct_0 @ X21))),
% 0.22/0.51      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.22/0.51  thf('61', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         (~ (r1_xboole_0 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0))
% 0.22/0.51          | ~ (l1_struct_0 @ X0)
% 0.22/0.51          | ~ (l1_struct_0 @ X1)
% 0.22/0.51          | (r1_tsep_1 @ X1 @ X0)
% 0.22/0.51          | ~ (l1_struct_0 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['59', '60'])).
% 0.22/0.51  thf('62', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((r1_tsep_1 @ X1 @ X0)
% 0.22/0.51          | ~ (l1_struct_0 @ X1)
% 0.22/0.51          | ~ (l1_struct_0 @ X0)
% 0.22/0.51          | ~ (r1_xboole_0 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0)))),
% 0.22/0.51      inference('simplify', [status(thm)], ['61'])).
% 0.22/0.51  thf('63', plain,
% 0.22/0.51      (((~ (l1_struct_0 @ sk_B)
% 0.22/0.51         | ~ (l1_struct_0 @ sk_D_2)
% 0.22/0.51         | (r1_tsep_1 @ sk_D_2 @ sk_B))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['58', '62'])).
% 0.22/0.51  thf('64', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.51      inference('demod', [status(thm)], ['50', '51'])).
% 0.22/0.51  thf('65', plain,
% 0.22/0.51      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_pre_topc @ X17))),
% 0.22/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.51  thf('66', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.51      inference('sup-', [status(thm)], ['64', '65'])).
% 0.22/0.51  thf('67', plain, ((l1_struct_0 @ sk_D_2)),
% 0.22/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.51  thf('68', plain,
% 0.22/0.51      (((r1_tsep_1 @ sk_D_2 @ sk_B)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.22/0.51      inference('demod', [status(thm)], ['63', '66', '67'])).
% 0.22/0.51  thf('69', plain,
% 0.22/0.51      (![X22 : $i, X23 : $i]:
% 0.22/0.51         (~ (l1_struct_0 @ X22)
% 0.22/0.51          | ~ (l1_struct_0 @ X23)
% 0.22/0.51          | (r1_tsep_1 @ X23 @ X22)
% 0.22/0.51          | ~ (r1_tsep_1 @ X22 @ X23))),
% 0.22/0.51      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.22/0.51  thf('70', plain,
% 0.22/0.51      ((((r1_tsep_1 @ sk_B @ sk_D_2)
% 0.22/0.51         | ~ (l1_struct_0 @ sk_B)
% 0.22/0.51         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['68', '69'])).
% 0.22/0.51  thf('71', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.51      inference('sup-', [status(thm)], ['64', '65'])).
% 0.22/0.51  thf('72', plain, ((l1_struct_0 @ sk_D_2)),
% 0.22/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.51  thf('73', plain,
% 0.22/0.51      (((r1_tsep_1 @ sk_B @ sk_D_2)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.22/0.51      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.22/0.51  thf('74', plain,
% 0.22/0.51      ((~ (r1_tsep_1 @ sk_B @ sk_D_2)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_2)))),
% 0.22/0.51      inference('split', [status(esa)], ['0'])).
% 0.22/0.51  thf('75', plain,
% 0.22/0.51      (((r1_tsep_1 @ sk_B @ sk_D_2)) | ~ ((r1_tsep_1 @ sk_D_2 @ sk_C_1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['73', '74'])).
% 0.22/0.52  thf('76', plain,
% 0.22/0.52      (((r1_tsep_1 @ sk_D_2 @ sk_B)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.22/0.52      inference('demod', [status(thm)], ['63', '66', '67'])).
% 0.22/0.52  thf('77', plain,
% 0.22/0.52      ((~ (r1_tsep_1 @ sk_D_2 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('78', plain,
% 0.22/0.52      (~ ((r1_tsep_1 @ sk_D_2 @ sk_C_1)) | ((r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['76', '77'])).
% 0.22/0.52  thf('79', plain,
% 0.22/0.52      (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D_2))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('80', plain,
% 0.22/0.52      (((r1_tsep_1 @ sk_C_1 @ sk_D_2)) | ((r1_tsep_1 @ sk_D_2 @ sk_C_1))),
% 0.22/0.52      inference('split', [status(esa)], ['4'])).
% 0.22/0.52  thf('81', plain, (((r1_tsep_1 @ sk_C_1 @ sk_D_2))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['75', '78', '79', '80'])).
% 0.22/0.52  thf('82', plain,
% 0.22/0.52      ((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1))),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['33', '81'])).
% 0.22/0.52  thf('83', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_C_1))
% 0.22/0.52          | (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_B)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['55', '56'])).
% 0.22/0.52  thf('84', plain,
% 0.22/0.52      ((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['82', '83'])).
% 0.22/0.52  thf('85', plain,
% 0.22/0.52      (![X6 : $i]:
% 0.22/0.52         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.52  thf('86', plain,
% 0.22/0.52      (![X6 : $i]:
% 0.22/0.52         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.52  thf('87', plain,
% 0.22/0.52      (![X20 : $i, X21 : $i]:
% 0.22/0.52         (~ (l1_struct_0 @ X20)
% 0.22/0.52          | ~ (r1_xboole_0 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X20))
% 0.22/0.52          | (r1_tsep_1 @ X21 @ X20)
% 0.22/0.52          | ~ (l1_struct_0 @ X21))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.22/0.52  thf('88', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (r1_xboole_0 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.22/0.52          | ~ (l1_struct_0 @ X0)
% 0.22/0.52          | ~ (l1_struct_0 @ X0)
% 0.22/0.52          | (r1_tsep_1 @ X0 @ X1)
% 0.22/0.52          | ~ (l1_struct_0 @ X1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['86', '87'])).
% 0.22/0.52  thf('89', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (l1_struct_0 @ X1)
% 0.22/0.52          | (r1_tsep_1 @ X0 @ X1)
% 0.22/0.52          | ~ (l1_struct_0 @ X0)
% 0.22/0.52          | ~ (r1_xboole_0 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['88'])).
% 0.22/0.52  thf('90', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (r1_xboole_0 @ (k2_struct_0 @ X1) @ (k2_struct_0 @ X0))
% 0.22/0.52          | ~ (l1_struct_0 @ X0)
% 0.22/0.52          | ~ (l1_struct_0 @ X1)
% 0.22/0.52          | (r1_tsep_1 @ X1 @ X0)
% 0.22/0.52          | ~ (l1_struct_0 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['85', '89'])).
% 0.22/0.52  thf('91', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((r1_tsep_1 @ X1 @ X0)
% 0.22/0.52          | ~ (l1_struct_0 @ X1)
% 0.22/0.52          | ~ (l1_struct_0 @ X0)
% 0.22/0.52          | ~ (r1_xboole_0 @ (k2_struct_0 @ X1) @ (k2_struct_0 @ X0)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['90'])).
% 0.22/0.52  thf('92', plain,
% 0.22/0.52      ((~ (l1_struct_0 @ sk_B)
% 0.22/0.52        | ~ (l1_struct_0 @ sk_D_2)
% 0.22/0.52        | (r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['84', '91'])).
% 0.22/0.52  thf('93', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.52      inference('sup-', [status(thm)], ['64', '65'])).
% 0.22/0.52  thf('94', plain, ((l1_struct_0 @ sk_D_2)),
% 0.22/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf('95', plain, ((r1_tsep_1 @ sk_D_2 @ sk_B)),
% 0.22/0.52      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.22/0.52  thf('96', plain,
% 0.22/0.52      (![X22 : $i, X23 : $i]:
% 0.22/0.52         (~ (l1_struct_0 @ X22)
% 0.22/0.52          | ~ (l1_struct_0 @ X23)
% 0.22/0.52          | (r1_tsep_1 @ X23 @ X22)
% 0.22/0.52          | ~ (r1_tsep_1 @ X22 @ X23))),
% 0.22/0.52      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.22/0.52  thf('97', plain,
% 0.22/0.52      (((r1_tsep_1 @ sk_B @ sk_D_2)
% 0.22/0.52        | ~ (l1_struct_0 @ sk_B)
% 0.22/0.52        | ~ (l1_struct_0 @ sk_D_2))),
% 0.22/0.52      inference('sup-', [status(thm)], ['95', '96'])).
% 0.22/0.52  thf('98', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.52      inference('sup-', [status(thm)], ['64', '65'])).
% 0.22/0.52  thf('99', plain, ((l1_struct_0 @ sk_D_2)),
% 0.22/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf('100', plain, ((r1_tsep_1 @ sk_B @ sk_D_2)),
% 0.22/0.52      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.22/0.52  thf('101', plain, (($false) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_2)))),
% 0.22/0.52      inference('demod', [status(thm)], ['1', '100'])).
% 0.22/0.52  thf('102', plain, ((r1_tsep_1 @ sk_D_2 @ sk_B)),
% 0.22/0.52      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.22/0.52  thf('103', plain,
% 0.22/0.52      ((~ (r1_tsep_1 @ sk_D_2 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('104', plain, (((r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['102', '103'])).
% 0.22/0.52  thf('105', plain,
% 0.22/0.52      (~ ((r1_tsep_1 @ sk_B @ sk_D_2)) | ~ ((r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('106', plain, (~ ((r1_tsep_1 @ sk_B @ sk_D_2))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['104', '105'])).
% 0.22/0.52  thf('107', plain, ($false),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['101', '106'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
