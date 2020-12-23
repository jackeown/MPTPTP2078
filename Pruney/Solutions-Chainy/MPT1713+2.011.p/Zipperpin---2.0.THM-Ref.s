%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R3Dvs5FSN8

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 321 expanded)
%              Number of leaves         :   36 ( 111 expanded)
%              Depth                    :   22
%              Number of atoms          :  674 (3206 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :   18 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_C_2 )
    | ( r1_tsep_1 @ sk_C_2 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tsep_1 @ sk_C_2 @ sk_B_1 )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_struct_0 @ X26 )
      | ~ ( l1_struct_0 @ X27 )
      | ( r1_tsep_1 @ X27 @ X26 )
      | ~ ( r1_tsep_1 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('6',plain,
    ( ( ( r1_tsep_1 @ sk_B_1 @ sk_C_2 )
      | ~ ( l1_struct_0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('12',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('20',plain,(
    l1_struct_0 @ sk_C_2 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_C_2 )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','13','20'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_struct_0 @ X24 )
      | ~ ( r1_tsep_1 @ X25 @ X24 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('23',plain,
    ( ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_2 ) )
      | ~ ( l1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('25',plain,(
    l1_struct_0 @ sk_C_2 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('26',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_2 ) )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['2','26'])).

thf('28',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('29',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_C_2 ) )
      | ~ ( l1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['1','29'])).

thf('31',plain,(
    l1_struct_0 @ sk_C_2 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('32',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('34',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('35',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_C_2 )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['3'])).

thf('36',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_struct_0 @ X24 )
      | ~ ( r1_tsep_1 @ X25 @ X24 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('37',plain,
    ( ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_2 ) )
      | ~ ( l1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('39',plain,(
    l1_struct_0 @ sk_C_2 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('40',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_2 ) )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['34','40'])).

thf('42',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('43',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_C_2 ) )
      | ~ ( l1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['33','43'])).

thf('45',plain,(
    l1_struct_0 @ sk_C_2 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('46',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('47',plain,(
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

thf('48',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( k3_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_C_2 ) ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    m1_pre_topc @ sk_B_1 @ sk_C_2 ),
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

thf('52',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_C_2 )
    | ( r1_tarski @ ( k2_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_C_2 ) )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['16','17'])).

thf('55',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('56',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('57',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('58',plain,
    ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_C_2 ) )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['50','58'])).

thf('60',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('61',plain,(
    ! [X23: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['59','63'])).

thf('65',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_B_1 )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ~ ( r1_tsep_1 @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( r1_tsep_1 @ sk_C_2 @ sk_B_1 )
    | ( r1_tsep_1 @ sk_B_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['3'])).

thf('70',plain,(
    r1_tsep_1 @ sk_C_2 @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['68','69'])).

thf('71',plain,(
    r1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['32','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('73',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_C_2 ) )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('75',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('77',plain,
    ( ~ ( l1_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('79',plain,(
    v2_struct_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['0','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R3Dvs5FSN8
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 78 iterations in 0.032s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.49  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.49  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.21/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
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
% 0.21/0.49  thf('0', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d3_struct_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X9 : $i]:
% 0.21/0.49         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X9 : $i]:
% 0.21/0.49         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_B_1 @ sk_C_2) | (r1_tsep_1 @ sk_C_2 @ sk_B_1))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_C_2 @ sk_B_1)) <= (((r1_tsep_1 @ sk_C_2 @ sk_B_1)))),
% 0.21/0.49      inference('split', [status(esa)], ['3'])).
% 0.21/0.49  thf(symmetry_r1_tsep_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.21/0.49       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X26 : $i, X27 : $i]:
% 0.21/0.49         (~ (l1_struct_0 @ X26)
% 0.21/0.49          | ~ (l1_struct_0 @ X27)
% 0.21/0.49          | (r1_tsep_1 @ X27 @ X26)
% 0.21/0.49          | ~ (r1_tsep_1 @ X26 @ X27))),
% 0.21/0.49      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      ((((r1_tsep_1 @ sk_B_1 @ sk_C_2)
% 0.21/0.49         | ~ (l1_struct_0 @ sk_B_1)
% 0.21/0.49         | ~ (l1_struct_0 @ sk_C_2))) <= (((r1_tsep_1 @ sk_C_2 @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.49  thf('7', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_m1_pre_topc, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X21 : $i, X22 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X21 @ X22)
% 0.21/0.49          | (l1_pre_topc @ X21)
% 0.21/0.49          | ~ (l1_pre_topc @ X22))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.49  thf('9', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('11', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf(dt_l1_pre_topc, axiom,
% 0.21/0.49    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.49  thf('13', plain, ((l1_struct_0 @ sk_B_1)),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('14', plain, ((m1_pre_topc @ sk_C_2 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X21 : $i, X22 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X21 @ X22)
% 0.21/0.49          | (l1_pre_topc @ X21)
% 0.21/0.49          | ~ (l1_pre_topc @ X22))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.49  thf('16', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_2))),
% 0.21/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('18', plain, ((l1_pre_topc @ sk_C_2)),
% 0.21/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.49  thf('20', plain, ((l1_struct_0 @ sk_C_2)),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_B_1 @ sk_C_2)) <= (((r1_tsep_1 @ sk_C_2 @ sk_B_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['6', '13', '20'])).
% 0.21/0.49  thf(d3_tsep_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_struct_0 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( l1_struct_0 @ B ) =>
% 0.21/0.49           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.21/0.49             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X24 : $i, X25 : $i]:
% 0.21/0.49         (~ (l1_struct_0 @ X24)
% 0.21/0.49          | ~ (r1_tsep_1 @ X25 @ X24)
% 0.21/0.49          | (r1_xboole_0 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))
% 0.21/0.49          | ~ (l1_struct_0 @ X25))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (((~ (l1_struct_0 @ sk_B_1)
% 0.21/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_2))
% 0.21/0.49         | ~ (l1_struct_0 @ sk_C_2))) <= (((r1_tsep_1 @ sk_C_2 @ sk_B_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf('24', plain, ((l1_struct_0 @ sk_B_1)),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('25', plain, ((l1_struct_0 @ sk_C_2)),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_2)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_C_2 @ sk_B_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      ((((r1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_2))
% 0.21/0.49         | ~ (l1_struct_0 @ sk_B_1))) <= (((r1_tsep_1 @ sk_C_2 @ sk_B_1)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['2', '26'])).
% 0.21/0.49  thf('28', plain, ((l1_struct_0 @ sk_B_1)),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (((r1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_2)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_C_2 @ sk_B_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      ((((r1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_C_2))
% 0.21/0.49         | ~ (l1_struct_0 @ sk_C_2))) <= (((r1_tsep_1 @ sk_C_2 @ sk_B_1)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['1', '29'])).
% 0.21/0.49  thf('31', plain, ((l1_struct_0 @ sk_C_2)),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (((r1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_C_2)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_C_2 @ sk_B_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (![X9 : $i]:
% 0.21/0.49         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (![X9 : $i]:
% 0.21/0.49         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_B_1 @ sk_C_2)) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_2)))),
% 0.21/0.49      inference('split', [status(esa)], ['3'])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (![X24 : $i, X25 : $i]:
% 0.21/0.49         (~ (l1_struct_0 @ X24)
% 0.21/0.49          | ~ (r1_tsep_1 @ X25 @ X24)
% 0.21/0.49          | (r1_xboole_0 @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X24))
% 0.21/0.49          | ~ (l1_struct_0 @ X25))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (((~ (l1_struct_0 @ sk_B_1)
% 0.21/0.49         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_2))
% 0.21/0.49         | ~ (l1_struct_0 @ sk_C_2))) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_2)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.49  thf('38', plain, ((l1_struct_0 @ sk_B_1)),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('39', plain, ((l1_struct_0 @ sk_C_2)),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      (((r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_2)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_2)))),
% 0.21/0.49      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      ((((r1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_2))
% 0.21/0.49         | ~ (l1_struct_0 @ sk_B_1))) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_2)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['34', '40'])).
% 0.21/0.49  thf('42', plain, ((l1_struct_0 @ sk_B_1)),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      (((r1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_2)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_2)))),
% 0.21/0.49      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      ((((r1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_C_2))
% 0.21/0.49         | ~ (l1_struct_0 @ sk_C_2))) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_2)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['33', '43'])).
% 0.21/0.49  thf('45', plain, ((l1_struct_0 @ sk_C_2)),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      (((r1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_C_2)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_2)))),
% 0.21/0.49      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.49  thf(d1_xboole_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.49  thf(t4_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.49            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.21/0.49          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      (((v1_xboole_0 @ 
% 0.21/0.49         (k3_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_C_2))))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_2)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['46', '49'])).
% 0.21/0.49  thf('51', plain, ((m1_pre_topc @ sk_B_1 @ sk_C_2)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d9_pre_topc, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( l1_pre_topc @ B ) =>
% 0.21/0.49           ( ( m1_pre_topc @ B @ A ) <=>
% 0.21/0.49             ( ( ![C:$i]:
% 0.21/0.49                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.49                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.21/0.49                     ( ?[D:$i]:
% 0.21/0.49                       ( ( m1_subset_1 @
% 0.21/0.49                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.49                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.21/0.49                         ( ( C ) =
% 0.21/0.49                           ( k9_subset_1 @
% 0.21/0.49                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 0.21/0.49               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.49  thf(zf_stmt_2, axiom,
% 0.21/0.49    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.49     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.21/0.49       ( ( ( C ) =
% 0.21/0.49           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 0.21/0.49         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.21/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_3, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( l1_pre_topc @ B ) =>
% 0.21/0.49           ( ( m1_pre_topc @ B @ A ) <=>
% 0.21/0.49             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 0.21/0.49               ( ![C:$i]:
% 0.21/0.49                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.49                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.21/0.49                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         (~ (l1_pre_topc @ X15)
% 0.21/0.49          | ~ (m1_pre_topc @ X15 @ X16)
% 0.21/0.49          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 0.21/0.49          | ~ (l1_pre_topc @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_C_2)
% 0.21/0.49        | (r1_tarski @ (k2_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_C_2))
% 0.21/0.49        | ~ (l1_pre_topc @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.49  thf('54', plain, ((l1_pre_topc @ sk_C_2)),
% 0.21/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('55', plain, ((l1_pre_topc @ sk_B_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf('56', plain,
% 0.21/0.49      ((r1_tarski @ (k2_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_C_2))),
% 0.21/0.49      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.21/0.49  thf(t28_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.49  thf('57', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i]:
% 0.21/0.49         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.49  thf('58', plain,
% 0.21/0.49      (((k3_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_C_2))
% 0.21/0.49         = (k2_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      (((v1_xboole_0 @ (k2_struct_0 @ sk_B_1)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_2)))),
% 0.21/0.49      inference('demod', [status(thm)], ['50', '58'])).
% 0.21/0.49  thf('60', plain,
% 0.21/0.49      (![X9 : $i]:
% 0.21/0.49         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.49  thf(fc2_struct_0, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.49       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.49  thf('61', plain,
% 0.21/0.49      (![X23 : $i]:
% 0.21/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X23))
% 0.21/0.49          | ~ (l1_struct_0 @ X23)
% 0.21/0.49          | (v2_struct_0 @ X23))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.49  thf('62', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.21/0.49          | ~ (l1_struct_0 @ X0)
% 0.21/0.49          | (v2_struct_0 @ X0)
% 0.21/0.49          | ~ (l1_struct_0 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.49  thf('63', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X0)
% 0.21/0.49          | ~ (l1_struct_0 @ X0)
% 0.21/0.49          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['62'])).
% 0.21/0.49  thf('64', plain,
% 0.21/0.49      (((~ (l1_struct_0 @ sk_B_1) | (v2_struct_0 @ sk_B_1)))
% 0.21/0.49         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_2)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['59', '63'])).
% 0.21/0.49  thf('65', plain, ((l1_struct_0 @ sk_B_1)),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('66', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_B_1)) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_2)))),
% 0.21/0.49      inference('demod', [status(thm)], ['64', '65'])).
% 0.21/0.49  thf('67', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('68', plain, (~ ((r1_tsep_1 @ sk_B_1 @ sk_C_2))),
% 0.21/0.49      inference('sup-', [status(thm)], ['66', '67'])).
% 0.21/0.49  thf('69', plain,
% 0.21/0.49      (((r1_tsep_1 @ sk_C_2 @ sk_B_1)) | ((r1_tsep_1 @ sk_B_1 @ sk_C_2))),
% 0.21/0.49      inference('split', [status(esa)], ['3'])).
% 0.21/0.49  thf('70', plain, (((r1_tsep_1 @ sk_C_2 @ sk_B_1))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['68', '69'])).
% 0.21/0.49  thf('71', plain,
% 0.21/0.49      ((r1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_C_2))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['32', '70'])).
% 0.21/0.49  thf('72', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.49  thf('73', plain,
% 0.21/0.49      ((v1_xboole_0 @ 
% 0.21/0.49        (k3_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_C_2)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.49  thf('74', plain,
% 0.21/0.49      (((k3_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_C_2))
% 0.21/0.49         = (k2_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.49  thf('75', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['73', '74'])).
% 0.21/0.49  thf('76', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X0)
% 0.21/0.49          | ~ (l1_struct_0 @ X0)
% 0.21/0.49          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['62'])).
% 0.21/0.49  thf('77', plain, ((~ (l1_struct_0 @ sk_B_1) | (v2_struct_0 @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['75', '76'])).
% 0.21/0.49  thf('78', plain, ((l1_struct_0 @ sk_B_1)),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('79', plain, ((v2_struct_0 @ sk_B_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['77', '78'])).
% 0.21/0.49  thf('80', plain, ($false), inference('demod', [status(thm)], ['0', '79'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
