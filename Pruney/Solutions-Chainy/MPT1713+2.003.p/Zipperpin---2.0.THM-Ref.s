%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4Kv0gjHyXc

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:15 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 373 expanded)
%              Number of leaves         :   43 ( 131 expanded)
%              Depth                    :   28
%              Number of atoms          :  834 (3509 expanded)
%              Number of equality atoms :   43 (  68 expanded)
%              Maximal formula depth    :   18 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_C_1 )
    | ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_B_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf(symmetry_r1_tsep_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_struct_0 @ B ) )
     => ( ( r1_tsep_1 @ A @ B )
       => ( r1_tsep_1 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( l1_struct_0 @ X35 )
      | ~ ( l1_struct_0 @ X36 )
      | ( r1_tsep_1 @ X36 @ X35 )
      | ~ ( r1_tsep_1 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_tsep_1])).

thf('6',plain,
    ( ( ( r1_tsep_1 @ sk_B_1 @ sk_C_1 )
      | ~ ( l1_struct_0 @ sk_B_1 )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
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
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( l1_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
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
    ! [X29: $i] :
      ( ( l1_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( l1_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
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
    ! [X29: $i] :
      ( ( l1_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('20',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['6','13','20'])).

thf(d3_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ( ( r1_tsep_1 @ A @ B )
          <=> ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('22',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( l1_struct_0 @ X33 )
      | ~ ( r1_tsep_1 @ X34 @ X33 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('23',plain,
    ( ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('25',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('26',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_C_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('28',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,
    ( ( r1_tsep_1 @ sk_B_1 @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('30',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( l1_struct_0 @ X33 )
      | ~ ( r1_tsep_1 @ X34 @ X33 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('31',plain,
    ( ( ~ ( l1_struct_0 @ sk_B_1 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('33',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('34',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('35',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('36',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
      = ( u1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('39',plain,(
    ! [X12: $i] :
      ( r1_xboole_0 @ X12 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('40',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('44',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('45',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','48'])).

thf('50',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['38','49'])).

thf('51',plain,
    ( ( ( k1_xboole_0
        = ( k3_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( l1_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['28','50'])).

thf('52',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('53',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k1_xboole_0
        = ( k3_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_C_1 ) ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['27','53'])).

thf('55',plain,(
    m1_pre_topc @ sk_B_1 @ sk_C_1 ),
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

thf('56',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_pre_topc @ X24 @ X25 )
      | ( r1_tarski @ ( k2_struct_0 @ X24 ) @ ( k2_struct_0 @ X25 ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('57',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( k2_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('59',plain,(
    l1_pre_topc @ sk_B_1 ),
    inference(demod,[status(thm)],['9','10'])).

thf('60',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('62',plain,
    ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('64',plain,
    ( ( k1_xboole_0
      = ( k2_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['54','62','63'])).

thf('65',plain,(
    ! [X18: $i] :
      ( ( ( k2_struct_0 @ X18 )
        = ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('66',plain,(
    ! [X32: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
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
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( l1_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_B_1 ) )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['64','68'])).

thf('70',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('71',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('72',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_B_1 )
   <= ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['69','74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ~ ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_B_1 )
    | ( r1_tsep_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('80',plain,(
    r1_tsep_1 @ sk_C_1 @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['78','79'])).

thf('81',plain,(
    r1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['26','80'])).

thf('82',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('83',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) )
    = ( u1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('85',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','48'])).

thf('87',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['2','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('90',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['1','90'])).

thf('92',plain,
    ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_B_1 ) @ ( k2_struct_0 @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('93',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('94',plain,
    ( k1_xboole_0
    = ( k2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('96',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['70','73'])).

thf('98',plain,(
    l1_struct_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('99',plain,(
    v2_struct_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,(
    $false ),
    inference(demod,[status(thm)],['0','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.16  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4Kv0gjHyXc
% 0.17/0.39  % Computer   : n010.cluster.edu
% 0.17/0.39  % Model      : x86_64 x86_64
% 0.17/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.39  % Memory     : 8042.1875MB
% 0.17/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.39  % CPULimit   : 60
% 0.17/0.39  % DateTime   : Tue Dec  1 11:15:30 EST 2020
% 0.17/0.39  % CPUTime    : 
% 0.17/0.39  % Running portfolio for 600 s
% 0.17/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.39  % Number of cores: 8
% 0.17/0.39  % Python version: Python 3.6.8
% 0.17/0.40  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 285 iterations in 0.095s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.41/0.60  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.41/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.41/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.41/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.41/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.41/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.60  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
% 0.41/0.60  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.41/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.60  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.41/0.60  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.41/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.41/0.60  thf(t22_tmap_1, conjecture,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.41/0.60           ( ![C:$i]:
% 0.41/0.60             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.41/0.60               ( ( m1_pre_topc @ B @ C ) =>
% 0.41/0.60                 ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i]:
% 0.41/0.60        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.41/0.60            ( l1_pre_topc @ A ) ) =>
% 0.41/0.60          ( ![B:$i]:
% 0.41/0.60            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.41/0.60              ( ![C:$i]:
% 0.41/0.60                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.41/0.60                  ( ( m1_pre_topc @ B @ C ) =>
% 0.41/0.60                    ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t22_tmap_1])).
% 0.41/0.60  thf('0', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(d3_struct_0, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.41/0.60  thf('1', plain,
% 0.41/0.60      (![X18 : $i]:
% 0.41/0.60         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.60  thf('2', plain,
% 0.41/0.60      (![X18 : $i]:
% 0.41/0.60         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.60  thf('3', plain,
% 0.41/0.60      (((r1_tsep_1 @ sk_B_1 @ sk_C_1) | (r1_tsep_1 @ sk_C_1 @ sk_B_1))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('4', plain,
% 0.41/0.60      (((r1_tsep_1 @ sk_C_1 @ sk_B_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.41/0.60      inference('split', [status(esa)], ['3'])).
% 0.41/0.60  thf(symmetry_r1_tsep_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.41/0.60       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.41/0.60  thf('5', plain,
% 0.41/0.60      (![X35 : $i, X36 : $i]:
% 0.41/0.60         (~ (l1_struct_0 @ X35)
% 0.41/0.60          | ~ (l1_struct_0 @ X36)
% 0.41/0.60          | (r1_tsep_1 @ X36 @ X35)
% 0.41/0.60          | ~ (r1_tsep_1 @ X35 @ X36))),
% 0.41/0.60      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.41/0.60  thf('6', plain,
% 0.41/0.60      ((((r1_tsep_1 @ sk_B_1 @ sk_C_1)
% 0.41/0.60         | ~ (l1_struct_0 @ sk_B_1)
% 0.41/0.60         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.60  thf('7', plain, ((m1_pre_topc @ sk_B_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(dt_m1_pre_topc, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.41/0.60  thf('8', plain,
% 0.41/0.60      (![X30 : $i, X31 : $i]:
% 0.41/0.60         (~ (m1_pre_topc @ X30 @ X31)
% 0.41/0.60          | (l1_pre_topc @ X30)
% 0.41/0.60          | ~ (l1_pre_topc @ X31))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.41/0.60  thf('9', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.60  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('11', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.60      inference('demod', [status(thm)], ['9', '10'])).
% 0.41/0.60  thf(dt_l1_pre_topc, axiom,
% 0.41/0.60    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.41/0.60  thf('12', plain,
% 0.41/0.60      (![X29 : $i]: ((l1_struct_0 @ X29) | ~ (l1_pre_topc @ X29))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.60  thf('13', plain, ((l1_struct_0 @ sk_B_1)),
% 0.41/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.60  thf('14', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('15', plain,
% 0.41/0.60      (![X30 : $i, X31 : $i]:
% 0.41/0.60         (~ (m1_pre_topc @ X30 @ X31)
% 0.41/0.60          | (l1_pre_topc @ X30)
% 0.41/0.60          | ~ (l1_pre_topc @ X31))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.41/0.60  thf('16', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.41/0.60  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('18', plain, ((l1_pre_topc @ sk_C_1)),
% 0.41/0.60      inference('demod', [status(thm)], ['16', '17'])).
% 0.41/0.60  thf('19', plain,
% 0.41/0.60      (![X29 : $i]: ((l1_struct_0 @ X29) | ~ (l1_pre_topc @ X29))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.41/0.60  thf('20', plain, ((l1_struct_0 @ sk_C_1)),
% 0.41/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.41/0.60  thf('21', plain,
% 0.41/0.60      (((r1_tsep_1 @ sk_B_1 @ sk_C_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.41/0.60      inference('demod', [status(thm)], ['6', '13', '20'])).
% 0.41/0.60  thf(d3_tsep_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_struct_0 @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( l1_struct_0 @ B ) =>
% 0.41/0.60           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.41/0.60             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.41/0.60  thf('22', plain,
% 0.41/0.60      (![X33 : $i, X34 : $i]:
% 0.41/0.60         (~ (l1_struct_0 @ X33)
% 0.41/0.60          | ~ (r1_tsep_1 @ X34 @ X33)
% 0.41/0.60          | (r1_xboole_0 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33))
% 0.41/0.60          | ~ (l1_struct_0 @ X34))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.41/0.60  thf('23', plain,
% 0.41/0.60      (((~ (l1_struct_0 @ sk_B_1)
% 0.41/0.60         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))
% 0.41/0.60         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.60  thf('24', plain, ((l1_struct_0 @ sk_B_1)),
% 0.41/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.60  thf('25', plain, ((l1_struct_0 @ sk_C_1)),
% 0.41/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.41/0.60  thf('26', plain,
% 0.41/0.60      (((r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1)))
% 0.41/0.60         <= (((r1_tsep_1 @ sk_C_1 @ sk_B_1)))),
% 0.41/0.60      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.41/0.60  thf('27', plain,
% 0.41/0.60      (![X18 : $i]:
% 0.41/0.60         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.60  thf('28', plain,
% 0.41/0.60      (![X18 : $i]:
% 0.41/0.60         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.60  thf('29', plain,
% 0.41/0.60      (((r1_tsep_1 @ sk_B_1 @ sk_C_1)) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.41/0.60      inference('split', [status(esa)], ['3'])).
% 0.41/0.60  thf('30', plain,
% 0.41/0.60      (![X33 : $i, X34 : $i]:
% 0.41/0.60         (~ (l1_struct_0 @ X33)
% 0.41/0.60          | ~ (r1_tsep_1 @ X34 @ X33)
% 0.41/0.60          | (r1_xboole_0 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X33))
% 0.41/0.60          | ~ (l1_struct_0 @ X34))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.41/0.60  thf('31', plain,
% 0.41/0.60      (((~ (l1_struct_0 @ sk_B_1)
% 0.41/0.60         | (r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))
% 0.41/0.60         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.41/0.60  thf('32', plain, ((l1_struct_0 @ sk_B_1)),
% 0.41/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.60  thf('33', plain, ((l1_struct_0 @ sk_C_1)),
% 0.41/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.41/0.60  thf('34', plain,
% 0.41/0.60      (((r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1)))
% 0.41/0.60         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.41/0.60      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.41/0.60  thf(t83_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.41/0.60  thf('35', plain,
% 0.41/0.60      (![X13 : $i, X14 : $i]:
% 0.41/0.60         (((k4_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.41/0.60      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.41/0.60  thf('36', plain,
% 0.41/0.60      ((((k4_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))
% 0.41/0.60          = (u1_struct_0 @ sk_B_1)))
% 0.41/0.60         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.41/0.60  thf(t48_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.41/0.60  thf('37', plain,
% 0.41/0.60      (![X10 : $i, X11 : $i]:
% 0.41/0.60         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.41/0.60           = (k3_xboole_0 @ X10 @ X11))),
% 0.41/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.41/0.60  thf('38', plain,
% 0.41/0.60      ((((k4_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_B_1))
% 0.41/0.60          = (k3_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))))
% 0.41/0.60         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['36', '37'])).
% 0.41/0.60  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.41/0.60  thf('39', plain, (![X12 : $i]: (r1_xboole_0 @ X12 @ k1_xboole_0)),
% 0.41/0.60      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.41/0.60  thf('40', plain,
% 0.41/0.60      (![X13 : $i, X14 : $i]:
% 0.41/0.60         (((k4_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.41/0.60      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.41/0.60  thf('41', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['39', '40'])).
% 0.41/0.60  thf('42', plain,
% 0.41/0.60      (![X10 : $i, X11 : $i]:
% 0.41/0.60         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.41/0.60           = (k3_xboole_0 @ X10 @ X11))),
% 0.41/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.41/0.60  thf('43', plain,
% 0.41/0.60      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['41', '42'])).
% 0.41/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.41/0.60  thf('44', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.41/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.41/0.60  thf(t28_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.41/0.60  thf('45', plain,
% 0.41/0.60      (![X7 : $i, X8 : $i]:
% 0.41/0.60         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.41/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.60  thf('46', plain,
% 0.41/0.60      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['44', '45'])).
% 0.41/0.60  thf(commutativity_k3_xboole_0, axiom,
% 0.41/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.41/0.60  thf('47', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.60  thf('48', plain,
% 0.41/0.60      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['46', '47'])).
% 0.41/0.60  thf('49', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.41/0.60      inference('demod', [status(thm)], ['43', '48'])).
% 0.41/0.60  thf('50', plain,
% 0.41/0.60      ((((k1_xboole_0)
% 0.41/0.60          = (k3_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))))
% 0.41/0.60         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.41/0.60      inference('demod', [status(thm)], ['38', '49'])).
% 0.41/0.60  thf('51', plain,
% 0.41/0.60      (((((k1_xboole_0)
% 0.41/0.60           = (k3_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1)))
% 0.41/0.60         | ~ (l1_struct_0 @ sk_B_1))) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['28', '50'])).
% 0.41/0.60  thf('52', plain, ((l1_struct_0 @ sk_B_1)),
% 0.41/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.60  thf('53', plain,
% 0.41/0.60      ((((k1_xboole_0)
% 0.41/0.60          = (k3_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))))
% 0.41/0.60         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.41/0.60      inference('demod', [status(thm)], ['51', '52'])).
% 0.41/0.60  thf('54', plain,
% 0.41/0.60      (((((k1_xboole_0)
% 0.41/0.60           = (k3_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_C_1)))
% 0.41/0.60         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['27', '53'])).
% 0.41/0.60  thf('55', plain, ((m1_pre_topc @ sk_B_1 @ sk_C_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(d9_pre_topc, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( l1_pre_topc @ B ) =>
% 0.41/0.60           ( ( m1_pre_topc @ B @ A ) <=>
% 0.41/0.60             ( ( ![C:$i]:
% 0.41/0.60                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.41/0.60                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.41/0.60                     ( ?[D:$i]:
% 0.41/0.60                       ( ( m1_subset_1 @
% 0.41/0.60                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.41/0.60                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.41/0.60                         ( ( C ) =
% 0.41/0.60                           ( k9_subset_1 @
% 0.41/0.60                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 0.41/0.60               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.41/0.60  thf(zf_stmt_2, axiom,
% 0.41/0.60    (![D:$i,C:$i,B:$i,A:$i]:
% 0.41/0.60     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.41/0.60       ( ( ( C ) =
% 0.41/0.60           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 0.41/0.60         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.41/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.41/0.60  thf(zf_stmt_3, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( l1_pre_topc @ A ) =>
% 0.41/0.60       ( ![B:$i]:
% 0.41/0.60         ( ( l1_pre_topc @ B ) =>
% 0.41/0.60           ( ( m1_pre_topc @ B @ A ) <=>
% 0.41/0.60             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 0.41/0.60               ( ![C:$i]:
% 0.41/0.60                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.41/0.60                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.41/0.60                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.60  thf('56', plain,
% 0.41/0.60      (![X24 : $i, X25 : $i]:
% 0.41/0.60         (~ (l1_pre_topc @ X24)
% 0.41/0.60          | ~ (m1_pre_topc @ X24 @ X25)
% 0.41/0.60          | (r1_tarski @ (k2_struct_0 @ X24) @ (k2_struct_0 @ X25))
% 0.41/0.60          | ~ (l1_pre_topc @ X25))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.41/0.60  thf('57', plain,
% 0.41/0.60      ((~ (l1_pre_topc @ sk_C_1)
% 0.41/0.60        | (r1_tarski @ (k2_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_C_1))
% 0.41/0.60        | ~ (l1_pre_topc @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['55', '56'])).
% 0.41/0.60  thf('58', plain, ((l1_pre_topc @ sk_C_1)),
% 0.41/0.60      inference('demod', [status(thm)], ['16', '17'])).
% 0.41/0.60  thf('59', plain, ((l1_pre_topc @ sk_B_1)),
% 0.41/0.60      inference('demod', [status(thm)], ['9', '10'])).
% 0.41/0.60  thf('60', plain,
% 0.41/0.60      ((r1_tarski @ (k2_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_C_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.41/0.60  thf('61', plain,
% 0.41/0.60      (![X7 : $i, X8 : $i]:
% 0.41/0.60         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.41/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.60  thf('62', plain,
% 0.41/0.60      (((k3_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_C_1))
% 0.41/0.60         = (k2_struct_0 @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['60', '61'])).
% 0.41/0.60  thf('63', plain, ((l1_struct_0 @ sk_C_1)),
% 0.41/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.41/0.60  thf('64', plain,
% 0.41/0.60      ((((k1_xboole_0) = (k2_struct_0 @ sk_B_1)))
% 0.41/0.60         <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.41/0.60      inference('demod', [status(thm)], ['54', '62', '63'])).
% 0.41/0.60  thf('65', plain,
% 0.41/0.60      (![X18 : $i]:
% 0.41/0.60         (((k2_struct_0 @ X18) = (u1_struct_0 @ X18)) | ~ (l1_struct_0 @ X18))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.41/0.60  thf(fc2_struct_0, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.41/0.60       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.41/0.60  thf('66', plain,
% 0.41/0.60      (![X32 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ (u1_struct_0 @ X32))
% 0.41/0.60          | ~ (l1_struct_0 @ X32)
% 0.41/0.60          | (v2_struct_0 @ X32))),
% 0.41/0.60      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.41/0.60  thf('67', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.41/0.60          | ~ (l1_struct_0 @ X0)
% 0.41/0.60          | (v2_struct_0 @ X0)
% 0.41/0.60          | ~ (l1_struct_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['65', '66'])).
% 0.41/0.60  thf('68', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v2_struct_0 @ X0)
% 0.41/0.60          | ~ (l1_struct_0 @ X0)
% 0.41/0.60          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['67'])).
% 0.41/0.60  thf('69', plain,
% 0.41/0.60      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.41/0.60         | ~ (l1_struct_0 @ sk_B_1)
% 0.41/0.60         | (v2_struct_0 @ sk_B_1))) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['64', '68'])).
% 0.41/0.60  thf('70', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 0.41/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.41/0.60  thf(d1_xboole_0, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.41/0.60  thf('71', plain,
% 0.41/0.60      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.60  thf(t7_ordinal1, axiom,
% 0.41/0.60    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.60  thf('72', plain,
% 0.41/0.60      (![X16 : $i, X17 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X16 @ X17) | ~ (r1_tarski @ X17 @ X16))),
% 0.41/0.60      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.41/0.60  thf('73', plain,
% 0.41/0.60      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['71', '72'])).
% 0.41/0.60  thf('74', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.60      inference('sup-', [status(thm)], ['70', '73'])).
% 0.41/0.60  thf('75', plain, ((l1_struct_0 @ sk_B_1)),
% 0.41/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.60  thf('76', plain,
% 0.41/0.60      (((v2_struct_0 @ sk_B_1)) <= (((r1_tsep_1 @ sk_B_1 @ sk_C_1)))),
% 0.41/0.60      inference('demod', [status(thm)], ['69', '74', '75'])).
% 0.41/0.60  thf('77', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('78', plain, (~ ((r1_tsep_1 @ sk_B_1 @ sk_C_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['76', '77'])).
% 0.41/0.60  thf('79', plain,
% 0.41/0.60      (((r1_tsep_1 @ sk_C_1 @ sk_B_1)) | ((r1_tsep_1 @ sk_B_1 @ sk_C_1))),
% 0.41/0.60      inference('split', [status(esa)], ['3'])).
% 0.41/0.60  thf('80', plain, (((r1_tsep_1 @ sk_C_1 @ sk_B_1))),
% 0.41/0.60      inference('sat_resolution*', [status(thm)], ['78', '79'])).
% 0.41/0.60  thf('81', plain,
% 0.41/0.60      ((r1_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))),
% 0.41/0.60      inference('simpl_trail', [status(thm)], ['26', '80'])).
% 0.41/0.60  thf('82', plain,
% 0.41/0.60      (![X13 : $i, X14 : $i]:
% 0.41/0.60         (((k4_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.41/0.60      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.41/0.60  thf('83', plain,
% 0.41/0.60      (((k4_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1))
% 0.41/0.60         = (u1_struct_0 @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['81', '82'])).
% 0.41/0.60  thf('84', plain,
% 0.41/0.60      (![X10 : $i, X11 : $i]:
% 0.41/0.60         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.41/0.60           = (k3_xboole_0 @ X10 @ X11))),
% 0.41/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.41/0.60  thf('85', plain,
% 0.41/0.60      (((k4_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_B_1))
% 0.41/0.60         = (k3_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1)))),
% 0.41/0.60      inference('sup+', [status(thm)], ['83', '84'])).
% 0.41/0.60  thf('86', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.41/0.60      inference('demod', [status(thm)], ['43', '48'])).
% 0.41/0.60  thf('87', plain,
% 0.41/0.60      (((k1_xboole_0)
% 0.41/0.60         = (k3_xboole_0 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1)))),
% 0.41/0.60      inference('demod', [status(thm)], ['85', '86'])).
% 0.41/0.60  thf('88', plain,
% 0.41/0.60      ((((k1_xboole_0)
% 0.41/0.60          = (k3_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1)))
% 0.41/0.60        | ~ (l1_struct_0 @ sk_B_1))),
% 0.41/0.60      inference('sup+', [status(thm)], ['2', '87'])).
% 0.41/0.60  thf('89', plain, ((l1_struct_0 @ sk_B_1)),
% 0.41/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.60  thf('90', plain,
% 0.41/0.60      (((k1_xboole_0)
% 0.41/0.60         = (k3_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_C_1)))),
% 0.41/0.60      inference('demod', [status(thm)], ['88', '89'])).
% 0.41/0.60  thf('91', plain,
% 0.41/0.60      ((((k1_xboole_0)
% 0.41/0.60          = (k3_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_C_1)))
% 0.41/0.60        | ~ (l1_struct_0 @ sk_C_1))),
% 0.41/0.60      inference('sup+', [status(thm)], ['1', '90'])).
% 0.41/0.60  thf('92', plain,
% 0.41/0.60      (((k3_xboole_0 @ (k2_struct_0 @ sk_B_1) @ (k2_struct_0 @ sk_C_1))
% 0.41/0.60         = (k2_struct_0 @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['60', '61'])).
% 0.41/0.60  thf('93', plain, ((l1_struct_0 @ sk_C_1)),
% 0.41/0.60      inference('sup-', [status(thm)], ['18', '19'])).
% 0.41/0.60  thf('94', plain, (((k1_xboole_0) = (k2_struct_0 @ sk_B_1))),
% 0.41/0.60      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.41/0.60  thf('95', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((v2_struct_0 @ X0)
% 0.41/0.60          | ~ (l1_struct_0 @ X0)
% 0.41/0.60          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['67'])).
% 0.41/0.60  thf('96', plain,
% 0.41/0.60      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.41/0.60        | ~ (l1_struct_0 @ sk_B_1)
% 0.41/0.60        | (v2_struct_0 @ sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['94', '95'])).
% 0.41/0.60  thf('97', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.60      inference('sup-', [status(thm)], ['70', '73'])).
% 0.41/0.60  thf('98', plain, ((l1_struct_0 @ sk_B_1)),
% 0.41/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.60  thf('99', plain, ((v2_struct_0 @ sk_B_1)),
% 0.41/0.60      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.41/0.60  thf('100', plain, ($false), inference('demod', [status(thm)], ['0', '99'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
