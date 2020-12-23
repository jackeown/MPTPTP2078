%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.P6IOLkCh9b

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  142 (1033 expanded)
%              Number of leaves         :   32 ( 313 expanded)
%              Depth                    :   24
%              Number of atoms          :  879 (13992 expanded)
%              Number of equality atoms :   11 (  54 expanded)
%              Maximal formula depth    :   18 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

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
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(split,[status(esa)],['3'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_struct_0 @ X23 )
      | ~ ( l1_struct_0 @ X24 )
      | ( r1_tsep_1 @ X24 @ X23 )
      | ~ ( r1_tsep_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('6',plain,
    ( ( ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_pre_topc @ sk_D_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( l1_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_D_2 ),
    inference(demod,[status(thm)],['9','10'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('12',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( l1_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('20',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['6','13','20'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_struct_0 @ X21 )
      | ~ ( r1_tsep_1 @ X22 @ X21 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('23',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('25',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('26',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['2','26'])).

thf('28',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('29',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( r1_tarski @ ( k2_struct_0 @ X13 ) @ ( k2_struct_0 @ X14 ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('34',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( l1_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['32','33','38'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['40'])).

thf(t64_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D )
        & ( r1_xboole_0 @ B @ D ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('42',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X6 )
      | ~ ( r1_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t64_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_B ) )
      | ~ ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['29','44'])).

thf('46',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('47',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('48',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('49',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_struct_0 @ X21 )
      | ~ ( r1_tsep_1 @ X22 @ X21 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('50',plain,
    ( ( ~ ( l1_struct_0 @ sk_D_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('52',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('53',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['47','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('56',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['46','56'])).

thf('58',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('59',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_B ) )
      | ~ ( r1_xboole_0 @ X0 @ ( k2_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('61',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('63',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('64',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_struct_0 @ X21 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) )
      | ( r1_tsep_1 @ X22 @ X21 )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( r1_tsep_1 @ X0 @ X1 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ( r1_tsep_1 @ X0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r1_tsep_1 @ X1 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tsep_1 @ X1 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_2 )
      | ( r1_tsep_1 @ sk_D_2 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['61','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['36','37'])).

thf('71',plain,(
    ! [X18: $i] :
      ( ( l1_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('72',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('74',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['69','72','73'])).

thf('75',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_struct_0 @ X23 )
      | ~ ( l1_struct_0 @ X24 )
      | ( r1_tsep_1 @ X24 @ X23 )
      | ~ ( r1_tsep_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('76',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_D_2 ) )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['70','71'])).

thf('78',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('79',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
   <= ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('81',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
    | ~ ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['69','72','73'])).

thf('83',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_C_1 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
    | ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('86',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('87',plain,(
    r1_tsep_1 @ sk_C_1 @ sk_D_2 ),
    inference('sat_resolution*',[status(thm)],['81','84','85','86'])).

thf('88',plain,(
    r1_xboole_0 @ ( u1_struct_0 @ sk_D_2 ) @ ( k2_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['45','87'])).

thf('89',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('90',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_struct_0 @ X21 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X21 ) )
      | ( r1_tsep_1 @ X22 @ X21 )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( u1_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r1_tsep_1 @ X1 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tsep_1 @ X1 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r1_xboole_0 @ ( u1_struct_0 @ X1 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_D_2 )
    | ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['88','92'])).

thf('94',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['70','71'])).

thf('95',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('96',plain,(
    r1_tsep_1 @ sk_D_2 @ sk_B ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ~ ( r1_tsep_1 @ sk_D_2 @ sk_B )
   <= ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('98',plain,(
    r1_tsep_1 @ sk_D_2 @ sk_B ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( r1_tsep_1 @ sk_B @ sk_D_2 )
    | ~ ( r1_tsep_1 @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('100',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference('sat_resolution*',[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_D_2 ) ),
    inference(simpl_trail,[status(thm)],['1','100'])).

thf('102',plain,(
    r1_tsep_1 @ sk_D_2 @ sk_B ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('103',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_struct_0 @ X23 )
      | ~ ( l1_struct_0 @ X24 )
      | ( r1_tsep_1 @ X24 @ X23 )
      | ~ ( r1_tsep_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('104',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_D_2 )
    | ~ ( l1_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['70','71'])).

thf('106',plain,(
    l1_struct_0 @ sk_D_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('107',plain,(
    r1_tsep_1 @ sk_B @ sk_D_2 ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,(
    $false ),
    inference(demod,[status(thm)],['101','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.P6IOLkCh9b
% 0.13/0.36  % Computer   : n018.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 12:37:57 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 90 iterations in 0.023s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.22/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.49  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.22/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.49  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.22/0.49  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.22/0.49  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.49  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.22/0.49  thf(t23_tmap_1, conjecture,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.22/0.49           ( ![C:$i]:
% 0.22/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.49               ( ![D:$i]:
% 0.22/0.49                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.49                   ( ( m1_pre_topc @ B @ C ) =>
% 0.22/0.49                     ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.22/0.49                       ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.22/0.49                         ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]:
% 0.22/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.49            ( l1_pre_topc @ A ) ) =>
% 0.22/0.49          ( ![B:$i]:
% 0.22/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.22/0.49              ( ![C:$i]:
% 0.22/0.49                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.49                  ( ![D:$i]:
% 0.22/0.49                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.22/0.49                      ( ( m1_pre_topc @ B @ C ) =>
% 0.22/0.49                        ( ( ( r1_tsep_1 @ B @ D ) & ( r1_tsep_1 @ D @ B ) ) | 
% 0.22/0.49                          ( ( ~( r1_tsep_1 @ C @ D ) ) & 
% 0.22/0.49                            ( ~( r1_tsep_1 @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t23_tmap_1])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      ((~ (r1_tsep_1 @ sk_B @ sk_D_2) | ~ (r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      ((~ (r1_tsep_1 @ sk_B @ sk_D_2)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_2)))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf(d3_struct_0, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X7 : $i]:
% 0.22/0.49         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (((r1_tsep_1 @ sk_C_1 @ sk_D_2) | (r1_tsep_1 @ sk_D_2 @ sk_C_1))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (((r1_tsep_1 @ sk_C_1 @ sk_D_2)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.22/0.49      inference('split', [status(esa)], ['3'])).
% 0.22/0.49  thf(symmetry_r1_tsep_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.22/0.49       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X23 : $i, X24 : $i]:
% 0.22/0.49         (~ (l1_struct_0 @ X23)
% 0.22/0.49          | ~ (l1_struct_0 @ X24)
% 0.22/0.49          | (r1_tsep_1 @ X24 @ X23)
% 0.22/0.49          | ~ (r1_tsep_1 @ X23 @ X24))),
% 0.22/0.49      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      ((((r1_tsep_1 @ sk_D_2 @ sk_C_1)
% 0.22/0.49         | ~ (l1_struct_0 @ sk_D_2)
% 0.22/0.49         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.49  thf('7', plain, ((m1_pre_topc @ sk_D_2 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(dt_m1_pre_topc, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X19 : $i, X20 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X19 @ X20)
% 0.22/0.49          | (l1_pre_topc @ X19)
% 0.22/0.49          | ~ (l1_pre_topc @ X20))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.49  thf('9', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D_2))),
% 0.22/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.49  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('11', plain, ((l1_pre_topc @ sk_D_2)),
% 0.22/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf(dt_l1_pre_topc, axiom,
% 0.22/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.49  thf('13', plain, ((l1_struct_0 @ sk_D_2)),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('14', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X19 : $i, X20 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X19 @ X20)
% 0.22/0.49          | (l1_pre_topc @ X19)
% 0.22/0.49          | ~ (l1_pre_topc @ X20))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.49  thf('16', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.49  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('18', plain, ((l1_pre_topc @ sk_C_1)),
% 0.22/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.49  thf('20', plain, ((l1_struct_0 @ sk_C_1)),
% 0.22/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (((r1_tsep_1 @ sk_D_2 @ sk_C_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.22/0.49      inference('demod', [status(thm)], ['6', '13', '20'])).
% 0.22/0.49  thf(d3_tsep_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_struct_0 @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( l1_struct_0 @ B ) =>
% 0.22/0.49           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.22/0.49             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (![X21 : $i, X22 : $i]:
% 0.22/0.49         (~ (l1_struct_0 @ X21)
% 0.22/0.49          | ~ (r1_tsep_1 @ X22 @ X21)
% 0.22/0.49          | (r1_xboole_0 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))
% 0.22/0.49          | ~ (l1_struct_0 @ X22))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (((~ (l1_struct_0 @ sk_D_2)
% 0.22/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 0.22/0.49         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.49  thf('24', plain, ((l1_struct_0 @ sk_D_2)),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('25', plain, ((l1_struct_0 @ sk_C_1)),
% 0.22/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 0.22/0.49         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.22/0.49      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      ((((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1))
% 0.22/0.49         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['2', '26'])).
% 0.22/0.49  thf('28', plain, ((l1_struct_0 @ sk_C_1)),
% 0.22/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1)))
% 0.22/0.49         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.22/0.49      inference('demod', [status(thm)], ['27', '28'])).
% 0.22/0.49  thf('30', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(d9_pre_topc, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( l1_pre_topc @ B ) =>
% 0.22/0.49           ( ( m1_pre_topc @ B @ A ) <=>
% 0.22/0.49             ( ( ![C:$i]:
% 0.22/0.49                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.49                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.22/0.49                     ( ?[D:$i]:
% 0.22/0.49                       ( ( m1_subset_1 @
% 0.22/0.49                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.22/0.49                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.22/0.49                         ( ( C ) =
% 0.22/0.49                           ( k9_subset_1 @
% 0.22/0.49                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 0.22/0.49               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.22/0.49  thf(zf_stmt_2, axiom,
% 0.22/0.49    (![D:$i,C:$i,B:$i,A:$i]:
% 0.22/0.49     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.22/0.49       ( ( ( C ) =
% 0.22/0.49           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 0.22/0.49         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.22/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_3, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( l1_pre_topc @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( l1_pre_topc @ B ) =>
% 0.22/0.49           ( ( m1_pre_topc @ B @ A ) <=>
% 0.22/0.49             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 0.22/0.49               ( ![C:$i]:
% 0.22/0.49                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.49                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.22/0.49                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('31', plain,
% 0.22/0.49      (![X13 : $i, X14 : $i]:
% 0.22/0.49         (~ (l1_pre_topc @ X13)
% 0.22/0.49          | ~ (m1_pre_topc @ X13 @ X14)
% 0.22/0.49          | (r1_tarski @ (k2_struct_0 @ X13) @ (k2_struct_0 @ X14))
% 0.22/0.49          | ~ (l1_pre_topc @ X14))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      ((~ (l1_pre_topc @ sk_C_1)
% 0.22/0.49        | (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))
% 0.22/0.49        | ~ (l1_pre_topc @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.49  thf('33', plain, ((l1_pre_topc @ sk_C_1)),
% 0.22/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.22/0.49  thf('34', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('35', plain,
% 0.22/0.49      (![X19 : $i, X20 : $i]:
% 0.22/0.49         (~ (m1_pre_topc @ X19 @ X20)
% 0.22/0.49          | (l1_pre_topc @ X19)
% 0.22/0.49          | ~ (l1_pre_topc @ X20))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.49  thf('36', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.49  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('38', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.49      inference('demod', [status(thm)], ['36', '37'])).
% 0.22/0.49  thf('39', plain,
% 0.22/0.49      ((r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))),
% 0.22/0.49      inference('demod', [status(thm)], ['32', '33', '38'])).
% 0.22/0.49  thf(d10_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.49  thf('40', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.49  thf('41', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.49      inference('simplify', [status(thm)], ['40'])).
% 0.22/0.49  thf(t64_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 0.22/0.49         ( r1_xboole_0 @ B @ D ) ) =>
% 0.22/0.49       ( r1_xboole_0 @ A @ C ) ))).
% 0.22/0.49  thf('42', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.49         ((r1_xboole_0 @ X3 @ X4)
% 0.22/0.49          | ~ (r1_tarski @ X3 @ X5)
% 0.22/0.49          | ~ (r1_tarski @ X4 @ X6)
% 0.22/0.49          | ~ (r1_xboole_0 @ X5 @ X6))),
% 0.22/0.49      inference('cnf', [status(esa)], [t64_xboole_1])).
% 0.22/0.49  thf('43', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (r1_xboole_0 @ X0 @ X1)
% 0.22/0.49          | ~ (r1_tarski @ X2 @ X1)
% 0.22/0.49          | (r1_xboole_0 @ X0 @ X2))),
% 0.22/0.49      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.49  thf('44', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_B))
% 0.22/0.49          | ~ (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_C_1)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['39', '43'])).
% 0.22/0.49  thf('45', plain,
% 0.22/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B)))
% 0.22/0.49         <= (((r1_tsep_1 @ sk_C_1 @ sk_D_2)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['29', '44'])).
% 0.22/0.49  thf('46', plain,
% 0.22/0.49      (![X7 : $i]:
% 0.22/0.49         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.49  thf('47', plain,
% 0.22/0.49      (![X7 : $i]:
% 0.22/0.49         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.49  thf('48', plain,
% 0.22/0.49      (((r1_tsep_1 @ sk_D_2 @ sk_C_1)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.22/0.49      inference('split', [status(esa)], ['3'])).
% 0.22/0.49  thf('49', plain,
% 0.22/0.49      (![X21 : $i, X22 : $i]:
% 0.22/0.49         (~ (l1_struct_0 @ X21)
% 0.22/0.49          | ~ (r1_tsep_1 @ X22 @ X21)
% 0.22/0.49          | (r1_xboole_0 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))
% 0.22/0.49          | ~ (l1_struct_0 @ X22))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.22/0.49  thf('50', plain,
% 0.22/0.49      (((~ (l1_struct_0 @ sk_D_2)
% 0.22/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 0.22/0.49         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.49  thf('51', plain, ((l1_struct_0 @ sk_D_2)),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('52', plain, ((l1_struct_0 @ sk_C_1)),
% 0.22/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.49  thf('53', plain,
% 0.22/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 0.22/0.49         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.22/0.49      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.22/0.49  thf('54', plain,
% 0.22/0.49      ((((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1))
% 0.22/0.49         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['47', '53'])).
% 0.22/0.49  thf('55', plain, ((l1_struct_0 @ sk_D_2)),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('56', plain,
% 0.22/0.49      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (u1_struct_0 @ sk_C_1)))
% 0.22/0.49         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.22/0.49      inference('demod', [status(thm)], ['54', '55'])).
% 0.22/0.49  thf('57', plain,
% 0.22/0.49      ((((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1))
% 0.22/0.49         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['46', '56'])).
% 0.22/0.49  thf('58', plain, ((l1_struct_0 @ sk_C_1)),
% 0.22/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.49  thf('59', plain,
% 0.22/0.49      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_C_1)))
% 0.22/0.49         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.22/0.49      inference('demod', [status(thm)], ['57', '58'])).
% 0.22/0.49  thf('60', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_B))
% 0.22/0.49          | ~ (r1_xboole_0 @ X0 @ (k2_struct_0 @ sk_C_1)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['39', '43'])).
% 0.22/0.49  thf('61', plain,
% 0.22/0.49      (((r1_xboole_0 @ (k2_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B)))
% 0.22/0.49         <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['59', '60'])).
% 0.22/0.49  thf('62', plain,
% 0.22/0.49      (![X7 : $i]:
% 0.22/0.49         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.49  thf('63', plain,
% 0.22/0.49      (![X7 : $i]:
% 0.22/0.49         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.49  thf('64', plain,
% 0.22/0.49      (![X21 : $i, X22 : $i]:
% 0.22/0.49         (~ (l1_struct_0 @ X21)
% 0.22/0.49          | ~ (r1_xboole_0 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))
% 0.22/0.49          | (r1_tsep_1 @ X22 @ X21)
% 0.22/0.49          | ~ (l1_struct_0 @ X22))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.22/0.49  thf('65', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r1_xboole_0 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1))
% 0.22/0.49          | ~ (l1_struct_0 @ X0)
% 0.22/0.49          | ~ (l1_struct_0 @ X0)
% 0.22/0.49          | (r1_tsep_1 @ X0 @ X1)
% 0.22/0.49          | ~ (l1_struct_0 @ X1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['63', '64'])).
% 0.22/0.49  thf('66', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (l1_struct_0 @ X1)
% 0.22/0.49          | (r1_tsep_1 @ X0 @ X1)
% 0.22/0.49          | ~ (l1_struct_0 @ X0)
% 0.22/0.49          | ~ (r1_xboole_0 @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X1)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['65'])).
% 0.22/0.49  thf('67', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r1_xboole_0 @ (k2_struct_0 @ X1) @ (k2_struct_0 @ X0))
% 0.22/0.49          | ~ (l1_struct_0 @ X0)
% 0.22/0.49          | ~ (l1_struct_0 @ X1)
% 0.22/0.49          | (r1_tsep_1 @ X1 @ X0)
% 0.22/0.49          | ~ (l1_struct_0 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['62', '66'])).
% 0.22/0.49  thf('68', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((r1_tsep_1 @ X1 @ X0)
% 0.22/0.49          | ~ (l1_struct_0 @ X1)
% 0.22/0.49          | ~ (l1_struct_0 @ X0)
% 0.22/0.49          | ~ (r1_xboole_0 @ (k2_struct_0 @ X1) @ (k2_struct_0 @ X0)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['67'])).
% 0.22/0.49  thf('69', plain,
% 0.22/0.49      (((~ (l1_struct_0 @ sk_B)
% 0.22/0.49         | ~ (l1_struct_0 @ sk_D_2)
% 0.22/0.49         | (r1_tsep_1 @ sk_D_2 @ sk_B))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['61', '68'])).
% 0.22/0.49  thf('70', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.49      inference('demod', [status(thm)], ['36', '37'])).
% 0.22/0.49  thf('71', plain,
% 0.22/0.49      (![X18 : $i]: ((l1_struct_0 @ X18) | ~ (l1_pre_topc @ X18))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.49  thf('72', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.49      inference('sup-', [status(thm)], ['70', '71'])).
% 0.22/0.49  thf('73', plain, ((l1_struct_0 @ sk_D_2)),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('74', plain,
% 0.22/0.49      (((r1_tsep_1 @ sk_D_2 @ sk_B)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.22/0.49      inference('demod', [status(thm)], ['69', '72', '73'])).
% 0.22/0.49  thf('75', plain,
% 0.22/0.49      (![X23 : $i, X24 : $i]:
% 0.22/0.49         (~ (l1_struct_0 @ X23)
% 0.22/0.49          | ~ (l1_struct_0 @ X24)
% 0.22/0.49          | (r1_tsep_1 @ X24 @ X23)
% 0.22/0.49          | ~ (r1_tsep_1 @ X23 @ X24))),
% 0.22/0.49      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.22/0.49  thf('76', plain,
% 0.22/0.49      ((((r1_tsep_1 @ sk_B @ sk_D_2)
% 0.22/0.49         | ~ (l1_struct_0 @ sk_B)
% 0.22/0.49         | ~ (l1_struct_0 @ sk_D_2))) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['74', '75'])).
% 0.22/0.49  thf('77', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.49      inference('sup-', [status(thm)], ['70', '71'])).
% 0.22/0.49  thf('78', plain, ((l1_struct_0 @ sk_D_2)),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('79', plain,
% 0.22/0.49      (((r1_tsep_1 @ sk_B @ sk_D_2)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.22/0.49      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.22/0.49  thf('80', plain,
% 0.22/0.49      ((~ (r1_tsep_1 @ sk_B @ sk_D_2)) <= (~ ((r1_tsep_1 @ sk_B @ sk_D_2)))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('81', plain,
% 0.22/0.49      (((r1_tsep_1 @ sk_B @ sk_D_2)) | ~ ((r1_tsep_1 @ sk_D_2 @ sk_C_1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['79', '80'])).
% 0.22/0.49  thf('82', plain,
% 0.22/0.49      (((r1_tsep_1 @ sk_D_2 @ sk_B)) <= (((r1_tsep_1 @ sk_D_2 @ sk_C_1)))),
% 0.22/0.49      inference('demod', [status(thm)], ['69', '72', '73'])).
% 0.22/0.49  thf('83', plain,
% 0.22/0.49      ((~ (r1_tsep_1 @ sk_D_2 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('84', plain,
% 0.22/0.49      (~ ((r1_tsep_1 @ sk_D_2 @ sk_C_1)) | ((r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['82', '83'])).
% 0.22/0.49  thf('85', plain,
% 0.22/0.49      (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)) | ~ ((r1_tsep_1 @ sk_B @ sk_D_2))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('86', plain,
% 0.22/0.49      (((r1_tsep_1 @ sk_C_1 @ sk_D_2)) | ((r1_tsep_1 @ sk_D_2 @ sk_C_1))),
% 0.22/0.49      inference('split', [status(esa)], ['3'])).
% 0.22/0.49  thf('87', plain, (((r1_tsep_1 @ sk_C_1 @ sk_D_2))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['81', '84', '85', '86'])).
% 0.22/0.49  thf('88', plain,
% 0.22/0.49      ((r1_xboole_0 @ (u1_struct_0 @ sk_D_2) @ (k2_struct_0 @ sk_B))),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['45', '87'])).
% 0.22/0.49  thf('89', plain,
% 0.22/0.49      (![X7 : $i]:
% 0.22/0.49         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.49  thf('90', plain,
% 0.22/0.49      (![X21 : $i, X22 : $i]:
% 0.22/0.49         (~ (l1_struct_0 @ X21)
% 0.22/0.49          | ~ (r1_xboole_0 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X21))
% 0.22/0.49          | (r1_tsep_1 @ X22 @ X21)
% 0.22/0.49          | ~ (l1_struct_0 @ X22))),
% 0.22/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.22/0.49  thf('91', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r1_xboole_0 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0))
% 0.22/0.49          | ~ (l1_struct_0 @ X0)
% 0.22/0.49          | ~ (l1_struct_0 @ X1)
% 0.22/0.49          | (r1_tsep_1 @ X1 @ X0)
% 0.22/0.49          | ~ (l1_struct_0 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['89', '90'])).
% 0.22/0.49  thf('92', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((r1_tsep_1 @ X1 @ X0)
% 0.22/0.49          | ~ (l1_struct_0 @ X1)
% 0.22/0.49          | ~ (l1_struct_0 @ X0)
% 0.22/0.49          | ~ (r1_xboole_0 @ (u1_struct_0 @ X1) @ (k2_struct_0 @ X0)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['91'])).
% 0.22/0.49  thf('93', plain,
% 0.22/0.49      ((~ (l1_struct_0 @ sk_B)
% 0.22/0.49        | ~ (l1_struct_0 @ sk_D_2)
% 0.22/0.49        | (r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['88', '92'])).
% 0.22/0.49  thf('94', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.49      inference('sup-', [status(thm)], ['70', '71'])).
% 0.22/0.49  thf('95', plain, ((l1_struct_0 @ sk_D_2)),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('96', plain, ((r1_tsep_1 @ sk_D_2 @ sk_B)),
% 0.22/0.49      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.22/0.49  thf('97', plain,
% 0.22/0.49      ((~ (r1_tsep_1 @ sk_D_2 @ sk_B)) <= (~ ((r1_tsep_1 @ sk_D_2 @ sk_B)))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('98', plain, (((r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.22/0.49      inference('sup-', [status(thm)], ['96', '97'])).
% 0.22/0.49  thf('99', plain,
% 0.22/0.49      (~ ((r1_tsep_1 @ sk_B @ sk_D_2)) | ~ ((r1_tsep_1 @ sk_D_2 @ sk_B))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('100', plain, (~ ((r1_tsep_1 @ sk_B @ sk_D_2))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['98', '99'])).
% 0.22/0.49  thf('101', plain, (~ (r1_tsep_1 @ sk_B @ sk_D_2)),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['1', '100'])).
% 0.22/0.49  thf('102', plain, ((r1_tsep_1 @ sk_D_2 @ sk_B)),
% 0.22/0.49      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.22/0.49  thf('103', plain,
% 0.22/0.49      (![X23 : $i, X24 : $i]:
% 0.22/0.49         (~ (l1_struct_0 @ X23)
% 0.22/0.49          | ~ (l1_struct_0 @ X24)
% 0.22/0.49          | (r1_tsep_1 @ X24 @ X23)
% 0.22/0.49          | ~ (r1_tsep_1 @ X23 @ X24))),
% 0.22/0.49      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.22/0.49  thf('104', plain,
% 0.22/0.49      (((r1_tsep_1 @ sk_B @ sk_D_2)
% 0.22/0.49        | ~ (l1_struct_0 @ sk_B)
% 0.22/0.49        | ~ (l1_struct_0 @ sk_D_2))),
% 0.22/0.49      inference('sup-', [status(thm)], ['102', '103'])).
% 0.22/0.49  thf('105', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.49      inference('sup-', [status(thm)], ['70', '71'])).
% 0.22/0.49  thf('106', plain, ((l1_struct_0 @ sk_D_2)),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('107', plain, ((r1_tsep_1 @ sk_B @ sk_D_2)),
% 0.22/0.49      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.22/0.49  thf('108', plain, ($false), inference('demod', [status(thm)], ['101', '107'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
