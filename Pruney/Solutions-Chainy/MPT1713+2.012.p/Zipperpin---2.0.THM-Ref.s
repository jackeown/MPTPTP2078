%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vwcj8t7EMA

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 328 expanded)
%              Number of leaves         :   35 ( 112 expanded)
%              Depth                    :   21
%              Number of atoms          :  698 (3267 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :   18 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

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
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_C_2 )
    | ( r1_tsep_1 @ sk_C_2 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_C_2 )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['3'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_struct_0 @ X27 )
      | ~ ( l1_struct_0 @ X28 )
      | ( r1_tsep_1 @ X28 @ X27 )
      | ~ ( r1_tsep_1 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('6',plain,
    ( ( ( r1_tsep_1 @ sk_C_2 @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_C_2 )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_pre_topc @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( l1_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['9','10'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('12',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,(
    l1_struct_0 @ sk_C_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( l1_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('20',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_tsep_1 @ sk_C_2 @ sk_B_1 )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['6','13','20'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_struct_0 @ X25 )
      | ~ ( r1_tsep_1 @ X26 @ X25 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('23',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_C_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('25',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('26',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['2','26'])).

thf('28',plain,(
    l1_struct_0 @ sk_C_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('29',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ( r1_tarski @ ( k2_struct_0 @ X16 ) @ ( k2_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_C_2 )
    | ( r1_tarski @ ( k2_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_C_2 ) )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_C_2 ),
    inference(demod,[status(thm)],['9','10'])).

thf('34',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('35',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X9 )
      | ( r1_xboole_0 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_struct_0 @ sk_C_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['29','37'])).

thf('39',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['1','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('41',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('43',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('44',plain,
    ( ( r1_tsep_1 @ sk_C_2 @ sk_B_1 )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('45',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_struct_0 @ X25 )
      | ~ ( r1_tsep_1 @ X26 @ X25 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('46',plain,
    ( ( ~ ( l1_struct_0 @ sk_C_2 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_struct_0 @ sk_C_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('48',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('49',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ sk_C_2 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['43','49'])).

thf('51',plain,(
    l1_struct_0 @ sk_C_2 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('52',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_C_2 ) @ ( u1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_struct_0 @ sk_C_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('54',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['42','54'])).

thf('56',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('57',plain,
    ( ( r1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('58',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('59',plain,(
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

thf('60',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('66',plain,(
    ! [X24: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['64','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('71',plain,
    ( ( v2_struct_0 @ sk_B_1 )
   <= ( r1_tsep_1 @ sk_C_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ~ ( r1_tsep_1 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_C_2 )
    | ( r1_tsep_1 @ sk_C_2 @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('75',plain,(
    r1_tsep_1 @ sk_B_1 @ sk_C_2 ),
    inference('sat_resolution*',[status(thm)],['73','74'])).

thf('76',plain,(
    r1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['41','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('78',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('80',plain,
    ( ~ ( l1_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('82',plain,(
    v2_struct_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['0','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vwcj8t7EMA
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:31:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 136 iterations in 0.039s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.50  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.50  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.20/0.50  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.50  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
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
% 0.20/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d3_struct_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X10 : $i]:
% 0.20/0.50         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X10 : $i]:
% 0.20/0.50         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_B_1 @ sk_C_2) | (r1_tsep_1 @ sk_C_2 @ sk_B_1))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_B_1 @ sk_C_2)) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_2)))),
% 0.20/0.50      inference('split', [status(esa)], ['3'])).
% 0.20/0.50  thf(symmetry_r1_tsep_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.20/0.50       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X27 : $i, X28 : $i]:
% 0.20/0.50         (~ (l1_struct_0 @ X27)
% 0.20/0.50          | ~ (l1_struct_0 @ X28)
% 0.20/0.50          | (r1_tsep_1 @ X28 @ X27)
% 0.20/0.50          | ~ (r1_tsep_1 @ X27 @ X28))),
% 0.20/0.50      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      ((((r1_tsep_1 @ sk_C_2 @ sk_B_1)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_C_2)
% 0.20/0.50         | ~ (l1_struct_0 @ sk_B_1))) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_2)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf('7', plain, ((m1_pre_topc @ sk_C_2 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_m1_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X22 : $i, X23 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X22 @ X23)
% 0.20/0.50          | (l1_pre_topc @ X22)
% 0.20/0.50          | ~ (l1_pre_topc @ X23))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.50  thf('9', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('11', plain, ((l1_pre_topc @ sk_C_2)),
% 0.20/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf(dt_l1_pre_topc, axiom,
% 0.20/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('13', plain, ((l1_struct_0 @ sk_C_2)),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('14', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X22 : $i, X23 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X22 @ X23)
% 0.20/0.50          | (l1_pre_topc @ X22)
% 0.20/0.50          | ~ (l1_pre_topc @ X23))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.50  thf('16', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('18', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.50      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.50  thf('20', plain, ((l1_struct_0 @ sk_B_1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_C_2 @ sk_B_1)) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_2)))),
% 0.20/0.50      inference('demod', [status(thm)], ['6', '13', '20'])).
% 0.20/0.50  thf(d3_tsep_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_struct_0 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( l1_struct_0 @ B ) =>
% 0.20/0.50           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.20/0.50             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X25 : $i, X26 : $i]:
% 0.20/0.50         (~ (l1_struct_0 @ X25)
% 0.20/0.50          | ~ (r1_tsep_1 @ X26 @ X25)
% 0.20/0.50          | (r1_xboole_0 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 0.20/0.50          | ~ (l1_struct_0 @ X26))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_C_2)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_B_1))
% 0.20/0.50         | ~ (l1_struct_0 @ sk_B_1))) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_2)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('24', plain, ((l1_struct_0 @ sk_C_2)),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('25', plain, ((l1_struct_0 @ sk_B_1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_B_1)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_2)))),
% 0.20/0.50      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      ((((r1_xboole_0 @ (k2_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_B_1))
% 0.20/0.50         | ~ (l1_struct_0 @ sk_C_2))) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_2)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['2', '26'])).
% 0.20/0.50  thf('28', plain, ((l1_struct_0 @ sk_C_2)),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (((r1_xboole_0 @ (k2_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_B_1)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_2)))),
% 0.20/0.50      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.50  thf('30', plain, ((m1_pre_topc @ sk_B_1 @ sk_C_2)),
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
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i]:
% 0.20/0.50         (~ (l1_pre_topc @ X16)
% 0.20/0.50          | ~ (m1_pre_topc @ X16 @ X17)
% 0.20/0.50          | (r1_tarski @ (k2_struct_0 @ X16) @ (k2_struct_0 @ X17))
% 0.20/0.50          | ~ (l1_pre_topc @ X17))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_C_2)
% 0.20/0.50        | (r1_tarski @ (k2_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_C_2))
% 0.20/0.50        | ~ (l1_pre_topc @ sk_B_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf('33', plain, ((l1_pre_topc @ sk_C_2)),
% 0.20/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('34', plain, ((l1_pre_topc @ sk_B_1)),
% 0.20/0.50      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      ((r1_tarski @ (k2_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_C_2))),
% 0.20/0.50      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.20/0.50  thf(t63_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.20/0.50       ( r1_xboole_0 @ A @ C ) ))).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.50         (~ (r1_tarski @ X7 @ X8)
% 0.20/0.50          | ~ (r1_xboole_0 @ X8 @ X9)
% 0.20/0.50          | (r1_xboole_0 @ X7 @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ X0)
% 0.20/0.50          | ~ (r1_xboole_0 @ (k2_struct_0 @ sk_C_2) @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (((r1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_B_1)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_2)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['29', '37'])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      ((((r1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_B_1))
% 0.20/0.50         | ~ (l1_struct_0 @ sk_B_1))) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_2)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['1', '38'])).
% 0.20/0.50  thf('40', plain, ((l1_struct_0 @ sk_B_1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (((r1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_B_1)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_2)))),
% 0.20/0.50      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X10 : $i]:
% 0.20/0.50         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (![X10 : $i]:
% 0.20/0.50         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_C_2 @ sk_B_1)) <= (((r1_tsep_1 @ sk_C_2 @ sk_B_1)))),
% 0.20/0.50      inference('split', [status(esa)], ['3'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (![X25 : $i, X26 : $i]:
% 0.20/0.50         (~ (l1_struct_0 @ X25)
% 0.20/0.50          | ~ (r1_tsep_1 @ X26 @ X25)
% 0.20/0.50          | (r1_xboole_0 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X25))
% 0.20/0.50          | ~ (l1_struct_0 @ X26))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_C_2)
% 0.20/0.50         | (r1_xboole_0 @ (u1_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_B_1))
% 0.20/0.50         | ~ (l1_struct_0 @ sk_B_1))) <= (((r1_tsep_1 @ sk_C_2 @ sk_B_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.50  thf('47', plain, ((l1_struct_0 @ sk_C_2)),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('48', plain, ((l1_struct_0 @ sk_B_1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (((r1_xboole_0 @ (u1_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_B_1)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C_2 @ sk_B_1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      ((((r1_xboole_0 @ (k2_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_B_1))
% 0.20/0.50         | ~ (l1_struct_0 @ sk_C_2))) <= (((r1_tsep_1 @ sk_C_2 @ sk_B_1)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['43', '49'])).
% 0.20/0.50  thf('51', plain, ((l1_struct_0 @ sk_C_2)),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      (((r1_xboole_0 @ (k2_struct_0 @ sk_C_2) @ (u1_struct_0 @ sk_B_1)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C_2 @ sk_B_1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.50  thf('53', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ X0)
% 0.20/0.50          | ~ (r1_xboole_0 @ (k2_struct_0 @ sk_C_2) @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      (((r1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_B_1)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C_2 @ sk_B_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      ((((r1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_B_1))
% 0.20/0.50         | ~ (l1_struct_0 @ sk_B_1))) <= (((r1_tsep_1 @ sk_C_2 @ sk_B_1)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['42', '54'])).
% 0.20/0.50  thf('56', plain, ((l1_struct_0 @ sk_B_1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      (((r1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_B_1)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C_2 @ sk_B_1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.50  thf(d1_xboole_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.50  thf(t3_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.50            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.50       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.50            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.50  thf('60', plain,
% 0.20/0.50      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X5 @ X3)
% 0.20/0.50          | ~ (r2_hidden @ X5 @ X6)
% 0.20/0.50          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v1_xboole_0 @ X0)
% 0.20/0.50          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.20/0.50          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.50  thf('62', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X0 @ X0) | (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['58', '61'])).
% 0.20/0.50  thf('63', plain,
% 0.20/0.50      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['62'])).
% 0.20/0.50  thf('64', plain,
% 0.20/0.50      (((v1_xboole_0 @ (k2_struct_0 @ sk_B_1)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C_2 @ sk_B_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['57', '63'])).
% 0.20/0.50  thf('65', plain,
% 0.20/0.50      (![X10 : $i]:
% 0.20/0.50         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.50  thf(fc2_struct_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.50       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.50  thf('66', plain,
% 0.20/0.50      (![X24 : $i]:
% 0.20/0.50         (~ (v1_xboole_0 @ (u1_struct_0 @ X24))
% 0.20/0.50          | ~ (l1_struct_0 @ X24)
% 0.20/0.50          | (v2_struct_0 @ X24))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.20/0.50          | ~ (l1_struct_0 @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | ~ (l1_struct_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.50  thf('68', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (l1_struct_0 @ X0)
% 0.20/0.50          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['67'])).
% 0.20/0.50  thf('69', plain,
% 0.20/0.50      (((~ (l1_struct_0 @ sk_B_1) | (v2_struct_0 @ sk_B_1)))
% 0.20/0.50         <= (((r1_tsep_1 @ sk_C_2 @ sk_B_1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['64', '68'])).
% 0.20/0.50  thf('70', plain, ((l1_struct_0 @ sk_B_1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('71', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_B_1)) <= (((r1_tsep_1 @ sk_C_2 @ sk_B_1)))),
% 0.20/0.50      inference('demod', [status(thm)], ['69', '70'])).
% 0.20/0.50  thf('72', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('73', plain, (~ ((r1_tsep_1 @ sk_C_2 @ sk_B_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['71', '72'])).
% 0.20/0.50  thf('74', plain,
% 0.20/0.50      (((r1_tsep_1 @ sk_B_1 @ sk_C_2)) | ((r1_tsep_1 @ sk_C_2 @ sk_B_1))),
% 0.20/0.50      inference('split', [status(esa)], ['3'])).
% 0.20/0.50  thf('75', plain, (((r1_tsep_1 @ sk_B_1 @ sk_C_2))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['73', '74'])).
% 0.20/0.50  thf('76', plain,
% 0.20/0.50      ((r1_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_B_1))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['41', '75'])).
% 0.20/0.50  thf('77', plain,
% 0.20/0.50      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['62'])).
% 0.20/0.50  thf('78', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_B_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['76', '77'])).
% 0.20/0.50  thf('79', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (l1_struct_0 @ X0)
% 0.20/0.50          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['67'])).
% 0.20/0.50  thf('80', plain, ((~ (l1_struct_0 @ sk_B_1) | (v2_struct_0 @ sk_B_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['78', '79'])).
% 0.20/0.50  thf('81', plain, ((l1_struct_0 @ sk_B_1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('82', plain, ((v2_struct_0 @ sk_B_1)),
% 0.20/0.50      inference('demod', [status(thm)], ['80', '81'])).
% 0.20/0.50  thf('83', plain, ($false), inference('demod', [status(thm)], ['0', '82'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
