%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WP5r6P2LEm

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 360 expanded)
%              Number of leaves         :   42 ( 126 expanded)
%              Depth                    :   27
%              Number of atoms          :  823 (3461 expanded)
%              Number of equality atoms :   47 (  73 expanded)
%              Maximal formula depth    :   18 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C_1 )
    | ( r1_tsep_1 @ sk_C_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_B )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_struct_0 @ X30 )
      | ~ ( l1_struct_0 @ X31 )
      | ( r1_tsep_1 @ X31 @ X30 )
      | ~ ( r1_tsep_1 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('6',plain,
    ( ( ( r1_tsep_1 @ sk_B @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( l1_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('12',plain,(
    ! [X24: $i] :
      ( ( l1_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( l1_pre_topc @ X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
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
    ! [X24: $i] :
      ( ( l1_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('20',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','13','20'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_struct_0 @ X28 )
      | ~ ( r1_tsep_1 @ X29 @ X28 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('23',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('25',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('26',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
      = ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('30',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('31',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('32',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_struct_0 @ X28 )
      | ~ ( r1_tsep_1 @ X29 @ X28 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('33',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('35',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('36',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
      = ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('41',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('42',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('45',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('46',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','50'])).

thf('52',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['40','51'])).

thf('53',plain,
    ( ( ( k1_xboole_0
        = ( k3_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['30','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('55',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k1_xboole_0
        = ( k3_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['29','55'])).

thf('57',plain,(
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

thf('58',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( r1_tarski @ ( k2_struct_0 @ X19 ) @ ( k2_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('59',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('61',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('62',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('63',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('64',plain,
    ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('66',plain,
    ( ( k1_xboole_0
      = ( k2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['56','64','65'])).

thf('67',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('68',plain,(
    ! [X27: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( l1_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['66','70'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('72',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('73',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('74',plain,
    ( ( v2_struct_0 @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('78',plain,(
    r1_tsep_1 @ sk_C_1 @ sk_B ),
    inference('sat_resolution*',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['28','78'])).

thf('80',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('81',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','50'])).

thf('83',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','83'])).

thf('85',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('86',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['1','86'])).

thf('88',plain,
    ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('89',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('90',plain,
    ( k1_xboole_0
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('92',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('94',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('95',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['0','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WP5r6P2LEm
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:49:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 154 iterations in 0.060s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.52  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.21/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.52  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.52  thf(t22_tmap_1, conjecture,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.52               ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.52                 ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i]:
% 0.21/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.52            ( l1_pre_topc @ A ) ) =>
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.52              ( ![C:$i]:
% 0.21/0.52                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.52                  ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.52                    ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t22_tmap_1])).
% 0.21/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(d3_struct_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X13 : $i]:
% 0.21/0.52         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X13 : $i]:
% 0.21/0.52         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (((r1_tsep_1 @ sk_B @ sk_C_1) | (r1_tsep_1 @ sk_C_1 @ sk_B))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (((r1_tsep_1 @ sk_C_1 @ sk_B)) <= (((r1_tsep_1 @ sk_C_1 @ sk_B)))),
% 0.21/0.52      inference('split', [status(esa)], ['3'])).
% 0.21/0.52  thf(symmetry_r1_tsep_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.21/0.52       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (![X30 : $i, X31 : $i]:
% 0.21/0.52         (~ (l1_struct_0 @ X30)
% 0.21/0.52          | ~ (l1_struct_0 @ X31)
% 0.21/0.52          | (r1_tsep_1 @ X31 @ X30)
% 0.21/0.52          | ~ (r1_tsep_1 @ X30 @ X31))),
% 0.21/0.52      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      ((((r1_tsep_1 @ sk_B @ sk_C_1)
% 0.21/0.52         | ~ (l1_struct_0 @ sk_B)
% 0.21/0.52         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.52  thf('7', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(dt_m1_pre_topc, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_pre_topc @ A ) =>
% 0.21/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X25 : $i, X26 : $i]:
% 0.21/0.52         (~ (m1_pre_topc @ X25 @ X26)
% 0.21/0.52          | (l1_pre_topc @ X25)
% 0.21/0.52          | ~ (l1_pre_topc @ X26))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.52  thf('9', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.52  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('11', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf(dt_l1_pre_topc, axiom,
% 0.21/0.52    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X24 : $i]: ((l1_struct_0 @ X24) | ~ (l1_pre_topc @ X24))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.52  thf('13', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf('14', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X25 : $i, X26 : $i]:
% 0.21/0.52         (~ (m1_pre_topc @ X25 @ X26)
% 0.21/0.52          | (l1_pre_topc @ X25)
% 0.21/0.52          | ~ (l1_pre_topc @ X26))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.52  thf('16', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('18', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.52      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X24 : $i]: ((l1_struct_0 @ X24) | ~ (l1_pre_topc @ X24))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.52  thf('20', plain, ((l1_struct_0 @ sk_C_1)),
% 0.21/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (((r1_tsep_1 @ sk_B @ sk_C_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['6', '13', '20'])).
% 0.21/0.52  thf(d3_tsep_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( l1_struct_0 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( l1_struct_0 @ B ) =>
% 0.21/0.52           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.21/0.52             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X28 : $i, X29 : $i]:
% 0.21/0.52         (~ (l1_struct_0 @ X28)
% 0.21/0.52          | ~ (r1_tsep_1 @ X29 @ X28)
% 0.21/0.52          | (r1_xboole_0 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))
% 0.21/0.52          | ~ (l1_struct_0 @ X29))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (((~ (l1_struct_0 @ sk_B)
% 0.21/0.52         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.52         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.52  thf('24', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf('25', plain, ((l1_struct_0 @ sk_C_1)),
% 0.21/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.52         <= (((r1_tsep_1 @ sk_C_1 @ sk_B)))),
% 0.21/0.52      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.21/0.52  thf(t83_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i]:
% 0.21/0.52         (((k4_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.21/0.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      ((((k4_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.52          = (u1_struct_0 @ sk_B)))
% 0.21/0.52         <= (((r1_tsep_1 @ sk_C_1 @ sk_B)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X13 : $i]:
% 0.21/0.52         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (![X13 : $i]:
% 0.21/0.52         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (((r1_tsep_1 @ sk_B @ sk_C_1)) <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.52      inference('split', [status(esa)], ['3'])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (![X28 : $i, X29 : $i]:
% 0.21/0.52         (~ (l1_struct_0 @ X28)
% 0.21/0.52          | ~ (r1_tsep_1 @ X29 @ X28)
% 0.21/0.52          | (r1_xboole_0 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))
% 0.21/0.52          | ~ (l1_struct_0 @ X29))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (((~ (l1_struct_0 @ sk_B)
% 0.21/0.52         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.52         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.52  thf('34', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf('35', plain, ((l1_struct_0 @ sk_C_1)),
% 0.21/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.52         <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.52      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i]:
% 0.21/0.52         (((k4_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.21/0.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      ((((k4_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.52          = (u1_struct_0 @ sk_B)))
% 0.21/0.52         <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.52  thf(t48_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.21/0.52           = (k3_xboole_0 @ X8 @ X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      ((((k4_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.21/0.52          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))))
% 0.21/0.52         <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['38', '39'])).
% 0.21/0.52  thf(t3_boole, axiom,
% 0.21/0.52    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.52  thf('41', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.21/0.52           = (k3_xboole_0 @ X8 @ X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['41', '42'])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.21/0.52           = (k3_xboole_0 @ X8 @ X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.52  thf(t36_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.21/0.52      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.52  thf(t3_xboole_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['44', '47'])).
% 0.21/0.52  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['48', '49'])).
% 0.21/0.52  thf('51', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['43', '50'])).
% 0.21/0.52  thf('52', plain,
% 0.21/0.52      ((((k1_xboole_0)
% 0.21/0.52          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))))
% 0.21/0.52         <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.52      inference('demod', [status(thm)], ['40', '51'])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (((((k1_xboole_0)
% 0.21/0.52           = (k3_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.52         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['30', '52'])).
% 0.21/0.52  thf('54', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf('55', plain,
% 0.21/0.52      ((((k1_xboole_0)
% 0.21/0.52          = (k3_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))))
% 0.21/0.52         <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.52      inference('demod', [status(thm)], ['53', '54'])).
% 0.21/0.52  thf('56', plain,
% 0.21/0.52      (((((k1_xboole_0)
% 0.21/0.52           = (k3_xboole_0 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1)))
% 0.21/0.52         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['29', '55'])).
% 0.21/0.52  thf('57', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
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
% 0.21/0.52  thf('58', plain,
% 0.21/0.52      (![X19 : $i, X20 : $i]:
% 0.21/0.52         (~ (l1_pre_topc @ X19)
% 0.21/0.52          | ~ (m1_pre_topc @ X19 @ X20)
% 0.21/0.52          | (r1_tarski @ (k2_struct_0 @ X19) @ (k2_struct_0 @ X20))
% 0.21/0.52          | ~ (l1_pre_topc @ X20))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      ((~ (l1_pre_topc @ sk_C_1)
% 0.21/0.52        | (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))
% 0.21/0.52        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.52  thf('60', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.52      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.52  thf('61', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.52  thf('62', plain,
% 0.21/0.52      ((r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))),
% 0.21/0.52      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.21/0.52  thf(t28_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.52  thf('63', plain,
% 0.21/0.52      (![X2 : $i, X3 : $i]:
% 0.21/0.52         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.21/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.52  thf('64', plain,
% 0.21/0.52      (((k3_xboole_0 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))
% 0.21/0.52         = (k2_struct_0 @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.52  thf('65', plain, ((l1_struct_0 @ sk_C_1)),
% 0.21/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.52  thf('66', plain,
% 0.21/0.52      ((((k1_xboole_0) = (k2_struct_0 @ sk_B)))
% 0.21/0.52         <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.52      inference('demod', [status(thm)], ['56', '64', '65'])).
% 0.21/0.52  thf('67', plain,
% 0.21/0.52      (![X13 : $i]:
% 0.21/0.52         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.52  thf(fc2_struct_0, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.52       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.52  thf('68', plain,
% 0.21/0.52      (![X27 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ (u1_struct_0 @ X27))
% 0.21/0.52          | ~ (l1_struct_0 @ X27)
% 0.21/0.52          | (v2_struct_0 @ X27))),
% 0.21/0.52      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.52  thf('69', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.21/0.52          | ~ (l1_struct_0 @ X0)
% 0.21/0.52          | (v2_struct_0 @ X0)
% 0.21/0.52          | ~ (l1_struct_0 @ X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.52  thf('70', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         ((v2_struct_0 @ X0)
% 0.21/0.52          | ~ (l1_struct_0 @ X0)
% 0.21/0.52          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['69'])).
% 0.21/0.52  thf('71', plain,
% 0.21/0.52      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.52         | ~ (l1_struct_0 @ sk_B)
% 0.21/0.52         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['66', '70'])).
% 0.21/0.52  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.52  thf('72', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.52      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.52  thf('73', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf('74', plain, (((v2_struct_0 @ sk_B)) <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.52      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.21/0.52  thf('75', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('76', plain, (~ ((r1_tsep_1 @ sk_B @ sk_C_1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['74', '75'])).
% 0.21/0.52  thf('77', plain,
% 0.21/0.52      (((r1_tsep_1 @ sk_C_1 @ sk_B)) | ((r1_tsep_1 @ sk_B @ sk_C_1))),
% 0.21/0.52      inference('split', [status(esa)], ['3'])).
% 0.21/0.52  thf('78', plain, (((r1_tsep_1 @ sk_C_1 @ sk_B))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['76', '77'])).
% 0.21/0.52  thf('79', plain,
% 0.21/0.52      (((k4_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.52         = (u1_struct_0 @ sk_B))),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['28', '78'])).
% 0.21/0.52  thf('80', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.21/0.52           = (k3_xboole_0 @ X8 @ X9))),
% 0.21/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.52  thf('81', plain,
% 0.21/0.52      (((k4_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.21/0.52         = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['79', '80'])).
% 0.21/0.52  thf('82', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['43', '50'])).
% 0.21/0.52  thf('83', plain,
% 0.21/0.52      (((k1_xboole_0)
% 0.21/0.52         = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.52      inference('demod', [status(thm)], ['81', '82'])).
% 0.21/0.52  thf('84', plain,
% 0.21/0.52      ((((k1_xboole_0)
% 0.21/0.52          = (k3_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.52        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.52      inference('sup+', [status(thm)], ['2', '83'])).
% 0.21/0.52  thf('85', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf('86', plain,
% 0.21/0.52      (((k1_xboole_0)
% 0.21/0.52         = (k3_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.52      inference('demod', [status(thm)], ['84', '85'])).
% 0.21/0.52  thf('87', plain,
% 0.21/0.52      ((((k1_xboole_0)
% 0.21/0.53          = (k3_xboole_0 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1)))
% 0.21/0.53        | ~ (l1_struct_0 @ sk_C_1))),
% 0.21/0.53      inference('sup+', [status(thm)], ['1', '86'])).
% 0.21/0.53  thf('88', plain,
% 0.21/0.53      (((k3_xboole_0 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))
% 0.21/0.53         = (k2_struct_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.53  thf('89', plain, ((l1_struct_0 @ sk_C_1)),
% 0.21/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.53  thf('90', plain, (((k1_xboole_0) = (k2_struct_0 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.21/0.53  thf('91', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (l1_struct_0 @ X0)
% 0.21/0.53          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['69'])).
% 0.21/0.53  thf('92', plain,
% 0.21/0.53      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.53        | ~ (l1_struct_0 @ sk_B)
% 0.21/0.53        | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['90', '91'])).
% 0.21/0.53  thf('93', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.53  thf('94', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('95', plain, ((v2_struct_0 @ sk_B)),
% 0.21/0.53      inference('demod', [status(thm)], ['92', '93', '94'])).
% 0.21/0.53  thf('96', plain, ($false), inference('demod', [status(thm)], ['0', '95'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
