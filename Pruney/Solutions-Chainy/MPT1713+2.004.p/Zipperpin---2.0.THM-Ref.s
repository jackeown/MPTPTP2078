%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b4YZpuM42M

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 372 expanded)
%              Number of leaves         :   41 ( 130 expanded)
%              Depth                    :   28
%              Number of atoms          :  830 (3519 expanded)
%              Number of equality atoms :   45 (  74 expanded)
%              Maximal formula depth    :   18 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tsep_1_type,type,(
    r1_tsep_1: $i > $i > $o )).

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
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
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
    ! [X29: $i,X30: $i] :
      ( ~ ( l1_struct_0 @ X29 )
      | ~ ( l1_struct_0 @ X30 )
      | ( r1_tsep_1 @ X30 @ X29 )
      | ~ ( r1_tsep_1 @ X29 @ X30 ) ) ),
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
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( l1_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
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
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('13',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_pre_topc @ X24 @ X25 )
      | ( l1_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
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
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
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
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_struct_0 @ X27 )
      | ~ ( r1_tsep_1 @ X28 @ X27 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
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

thf('27',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('28',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('29',plain,
    ( ( r1_tsep_1 @ sk_B @ sk_C_1 )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('30',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_struct_0 @ X27 )
      | ~ ( r1_tsep_1 @ X28 @ X27 )
      | ( r1_xboole_0 @ ( u1_struct_0 @ X28 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_tsep_1])).

thf('31',plain,
    ( ( ~ ( l1_struct_0 @ sk_B )
      | ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('33',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('34',plain,
    ( ( r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('36',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
      = ( u1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('39',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('40',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','52'])).

thf('54',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['38','53'])).

thf('55',plain,
    ( ( ( k1_xboole_0
        = ( k3_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['28','54'])).

thf('56',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('57',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( k1_xboole_0
        = ( k3_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) ) )
      | ~ ( l1_struct_0 @ sk_C_1 ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['27','57'])).

thf('59',plain,(
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

thf('60',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( r1_tarski @ ( k2_struct_0 @ X18 ) @ ( k2_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('61',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('63',plain,(
    l1_pre_topc @ sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('64',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('65',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('66',plain,
    ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('68',plain,
    ( ( k1_xboole_0
      = ( k2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['58','66','67'])).

thf('69',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('70',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( l1_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['68','72'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('74',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('75',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('76',plain,
    ( ( v2_struct_0 @ sk_B )
   <= ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ~ ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( r1_tsep_1 @ sk_C_1 @ sk_B )
    | ( r1_tsep_1 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('80',plain,(
    r1_tsep_1 @ sk_C_1 @ sk_B ),
    inference('sat_resolution*',[status(thm)],['78','79'])).

thf('81',plain,(
    r1_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['26','80'])).

thf('82',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('83',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) )
    = ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('85',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) )
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','52'])).

thf('87',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('90',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['1','90'])).

thf('92',plain,
    ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('93',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('94',plain,
    ( k1_xboole_0
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('96',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('98',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('99',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,(
    $false ),
    inference(demod,[status(thm)],['0','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b4YZpuM42M
% 0.15/0.34  % Computer   : n020.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 12:58:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 285 iterations in 0.071s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.52  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.21/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(r1_tsep_1_type, type, r1_tsep_1: $i > $i > $o).
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
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.53              ( ![C:$i]:
% 0.21/0.53                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.53                  ( ( m1_pre_topc @ B @ C ) =>
% 0.21/0.53                    ( ( ~( r1_tsep_1 @ B @ C ) ) & ( ~( r1_tsep_1 @ C @ B ) ) ) ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t22_tmap_1])).
% 0.21/0.53  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d3_struct_0, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X12 : $i]:
% 0.21/0.53         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X12 : $i]:
% 0.21/0.53         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (((r1_tsep_1 @ sk_B @ sk_C_1) | (r1_tsep_1 @ sk_C_1 @ sk_B))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (((r1_tsep_1 @ sk_C_1 @ sk_B)) <= (((r1_tsep_1 @ sk_C_1 @ sk_B)))),
% 0.21/0.53      inference('split', [status(esa)], ['3'])).
% 0.21/0.53  thf(symmetry_r1_tsep_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( l1_struct_0 @ A ) & ( l1_struct_0 @ B ) ) =>
% 0.21/0.53       ( ( r1_tsep_1 @ A @ B ) => ( r1_tsep_1 @ B @ A ) ) ))).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X29 : $i, X30 : $i]:
% 0.21/0.53         (~ (l1_struct_0 @ X29)
% 0.21/0.53          | ~ (l1_struct_0 @ X30)
% 0.21/0.53          | (r1_tsep_1 @ X30 @ X29)
% 0.21/0.53          | ~ (r1_tsep_1 @ X29 @ X30))),
% 0.21/0.53      inference('cnf', [status(esa)], [symmetry_r1_tsep_1])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      ((((r1_tsep_1 @ sk_B @ sk_C_1)
% 0.21/0.53         | ~ (l1_struct_0 @ sk_B)
% 0.21/0.53         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.53  thf('7', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(dt_m1_pre_topc, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X24 : $i, X25 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X24 @ X25)
% 0.21/0.53          | (l1_pre_topc @ X24)
% 0.21/0.53          | ~ (l1_pre_topc @ X25))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.53  thf('9', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.53  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('11', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf(dt_l1_pre_topc, axiom,
% 0.21/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.53  thf('13', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('14', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X24 : $i, X25 : $i]:
% 0.21/0.53         (~ (m1_pre_topc @ X24 @ X25)
% 0.21/0.53          | (l1_pre_topc @ X24)
% 0.21/0.53          | ~ (l1_pre_topc @ X25))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.53  thf('16', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.53  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('18', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.53      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.53  thf('20', plain, ((l1_struct_0 @ sk_C_1)),
% 0.21/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (((r1_tsep_1 @ sk_B @ sk_C_1)) <= (((r1_tsep_1 @ sk_C_1 @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['6', '13', '20'])).
% 0.21/0.53  thf(d3_tsep_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_struct_0 @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( l1_struct_0 @ B ) =>
% 0.21/0.53           ( ( r1_tsep_1 @ A @ B ) <=>
% 0.21/0.53             ( r1_xboole_0 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X27 : $i, X28 : $i]:
% 0.21/0.53         (~ (l1_struct_0 @ X27)
% 0.21/0.53          | ~ (r1_tsep_1 @ X28 @ X27)
% 0.21/0.53          | (r1_xboole_0 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 0.21/0.53          | ~ (l1_struct_0 @ X28))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (((~ (l1_struct_0 @ sk_B)
% 0.21/0.53         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.53         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_C_1 @ sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.53  thf('24', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('25', plain, ((l1_struct_0 @ sk_C_1)),
% 0.21/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.53         <= (((r1_tsep_1 @ sk_C_1 @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X12 : $i]:
% 0.21/0.53         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.53  thf('28', plain,
% 0.21/0.53      (![X12 : $i]:
% 0.21/0.53         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.53  thf('29', plain,
% 0.21/0.53      (((r1_tsep_1 @ sk_B @ sk_C_1)) <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.53      inference('split', [status(esa)], ['3'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (![X27 : $i, X28 : $i]:
% 0.21/0.53         (~ (l1_struct_0 @ X27)
% 0.21/0.53          | ~ (r1_tsep_1 @ X28 @ X27)
% 0.21/0.53          | (r1_xboole_0 @ (u1_struct_0 @ X28) @ (u1_struct_0 @ X27))
% 0.21/0.53          | ~ (l1_struct_0 @ X28))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tsep_1])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      (((~ (l1_struct_0 @ sk_B)
% 0.21/0.53         | (r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.53         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('33', plain, ((l1_struct_0 @ sk_C_1)),
% 0.21/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      (((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.53         <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.53      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.21/0.53  thf(t83_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.53  thf('35', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i]:
% 0.21/0.53         (((k4_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.53  thf('36', plain,
% 0.21/0.53      ((((k4_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.53          = (u1_struct_0 @ sk_B)))
% 0.21/0.53         <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.53  thf(t48_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.21/0.53           = (k3_xboole_0 @ X6 @ X7))),
% 0.21/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      ((((k4_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.21/0.53          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))))
% 0.21/0.53         <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['36', '37'])).
% 0.21/0.53  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.53  thf('39', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.21/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i]:
% 0.21/0.53         (((k4_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.53  thf('41', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.21/0.53           = (k3_xboole_0 @ X6 @ X7))),
% 0.21/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['41', '42'])).
% 0.21/0.53  thf('44', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.21/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.53  thf(symmetry_r1_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.21/0.53  thf('45', plain,
% 0.21/0.53      (![X2 : $i, X3 : $i]:
% 0.21/0.53         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.53  thf('46', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.53  thf('47', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i]:
% 0.21/0.53         (((k4_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.21/0.53           = (k3_xboole_0 @ X6 @ X7))),
% 0.21/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.53  thf('50', plain,
% 0.21/0.53      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['48', '49'])).
% 0.21/0.53  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.53  thf('51', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['50', '51'])).
% 0.21/0.53  thf('53', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['43', '52'])).
% 0.21/0.53  thf('54', plain,
% 0.21/0.53      ((((k1_xboole_0)
% 0.21/0.53          = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))))
% 0.21/0.53         <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.53      inference('demod', [status(thm)], ['38', '53'])).
% 0.21/0.53  thf('55', plain,
% 0.21/0.53      (((((k1_xboole_0)
% 0.21/0.53           = (k3_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.53         | ~ (l1_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['28', '54'])).
% 0.21/0.53  thf('56', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('57', plain,
% 0.21/0.53      ((((k1_xboole_0)
% 0.21/0.53          = (k3_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))))
% 0.21/0.53         <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.53      inference('demod', [status(thm)], ['55', '56'])).
% 0.21/0.53  thf('58', plain,
% 0.21/0.53      (((((k1_xboole_0)
% 0.21/0.53           = (k3_xboole_0 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1)))
% 0.21/0.53         | ~ (l1_struct_0 @ sk_C_1))) <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['27', '57'])).
% 0.21/0.53  thf('59', plain, ((m1_pre_topc @ sk_B @ sk_C_1)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d9_pre_topc, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( l1_pre_topc @ B ) =>
% 0.21/0.53           ( ( m1_pre_topc @ B @ A ) <=>
% 0.21/0.53             ( ( ![C:$i]:
% 0.21/0.53                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.53                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.21/0.53                     ( ?[D:$i]:
% 0.21/0.53                       ( ( m1_subset_1 @
% 0.21/0.53                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.21/0.53                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.21/0.53                         ( ( C ) =
% 0.21/0.53                           ( k9_subset_1 @
% 0.21/0.53                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 0.21/0.53               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.53  thf(zf_stmt_2, axiom,
% 0.21/0.53    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.53     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.21/0.53       ( ( ( C ) =
% 0.21/0.53           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 0.21/0.53         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.21/0.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_3, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( l1_pre_topc @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( l1_pre_topc @ B ) =>
% 0.21/0.53           ( ( m1_pre_topc @ B @ A ) <=>
% 0.21/0.53             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 0.21/0.53               ( ![C:$i]:
% 0.21/0.53                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.53                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.21/0.53                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.53  thf('60', plain,
% 0.21/0.53      (![X18 : $i, X19 : $i]:
% 0.21/0.53         (~ (l1_pre_topc @ X18)
% 0.21/0.53          | ~ (m1_pre_topc @ X18 @ X19)
% 0.21/0.53          | (r1_tarski @ (k2_struct_0 @ X18) @ (k2_struct_0 @ X19))
% 0.21/0.53          | ~ (l1_pre_topc @ X19))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.53  thf('61', plain,
% 0.21/0.53      ((~ (l1_pre_topc @ sk_C_1)
% 0.21/0.53        | (r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))
% 0.21/0.53        | ~ (l1_pre_topc @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.53  thf('62', plain, ((l1_pre_topc @ sk_C_1)),
% 0.21/0.53      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.53  thf('63', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf('64', plain,
% 0.21/0.53      ((r1_tarski @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))),
% 0.21/0.53      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.21/0.53  thf(t28_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.53  thf('65', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i]:
% 0.21/0.53         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.21/0.53      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.53  thf('66', plain,
% 0.21/0.53      (((k3_xboole_0 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))
% 0.21/0.53         = (k2_struct_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.53  thf('67', plain, ((l1_struct_0 @ sk_C_1)),
% 0.21/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.53  thf('68', plain,
% 0.21/0.53      ((((k1_xboole_0) = (k2_struct_0 @ sk_B)))
% 0.21/0.53         <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.53      inference('demod', [status(thm)], ['58', '66', '67'])).
% 0.21/0.53  thf('69', plain,
% 0.21/0.53      (![X12 : $i]:
% 0.21/0.53         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.21/0.53  thf(fc2_struct_0, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.53       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.53  thf('70', plain,
% 0.21/0.53      (![X26 : $i]:
% 0.21/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X26))
% 0.21/0.53          | ~ (l1_struct_0 @ X26)
% 0.21/0.53          | (v2_struct_0 @ X26))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.53  thf('71', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.21/0.53          | ~ (l1_struct_0 @ X0)
% 0.21/0.53          | (v2_struct_0 @ X0)
% 0.21/0.53          | ~ (l1_struct_0 @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.53  thf('72', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (l1_struct_0 @ X0)
% 0.21/0.53          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['71'])).
% 0.21/0.53  thf('73', plain,
% 0.21/0.53      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.53         | ~ (l1_struct_0 @ sk_B)
% 0.21/0.53         | (v2_struct_0 @ sk_B))) <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['68', '72'])).
% 0.21/0.53  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.53  thf('74', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.53  thf('75', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('76', plain, (((v2_struct_0 @ sk_B)) <= (((r1_tsep_1 @ sk_B @ sk_C_1)))),
% 0.21/0.53      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.21/0.53  thf('77', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('78', plain, (~ ((r1_tsep_1 @ sk_B @ sk_C_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['76', '77'])).
% 0.21/0.53  thf('79', plain,
% 0.21/0.53      (((r1_tsep_1 @ sk_C_1 @ sk_B)) | ((r1_tsep_1 @ sk_B @ sk_C_1))),
% 0.21/0.53      inference('split', [status(esa)], ['3'])).
% 0.21/0.53  thf('80', plain, (((r1_tsep_1 @ sk_C_1 @ sk_B))),
% 0.21/0.53      inference('sat_resolution*', [status(thm)], ['78', '79'])).
% 0.21/0.53  thf('81', plain,
% 0.21/0.53      ((r1_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))),
% 0.21/0.53      inference('simpl_trail', [status(thm)], ['26', '80'])).
% 0.21/0.53  thf('82', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i]:
% 0.21/0.53         (((k4_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.53  thf('83', plain,
% 0.21/0.53      (((k4_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1))
% 0.21/0.53         = (u1_struct_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['81', '82'])).
% 0.21/0.53  thf('84', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.21/0.53           = (k3_xboole_0 @ X6 @ X7))),
% 0.21/0.53      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.53  thf('85', plain,
% 0.21/0.53      (((k4_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_B))
% 0.21/0.53         = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['83', '84'])).
% 0.21/0.53  thf('86', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['43', '52'])).
% 0.21/0.53  thf('87', plain,
% 0.21/0.53      (((k1_xboole_0)
% 0.21/0.53         = (k3_xboole_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.53      inference('demod', [status(thm)], ['85', '86'])).
% 0.21/0.53  thf('88', plain,
% 0.21/0.53      ((((k1_xboole_0)
% 0.21/0.53          = (k3_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))
% 0.21/0.53        | ~ (l1_struct_0 @ sk_B))),
% 0.21/0.53      inference('sup+', [status(thm)], ['2', '87'])).
% 0.21/0.53  thf('89', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('90', plain,
% 0.21/0.53      (((k1_xboole_0)
% 0.21/0.53         = (k3_xboole_0 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))),
% 0.21/0.53      inference('demod', [status(thm)], ['88', '89'])).
% 0.21/0.53  thf('91', plain,
% 0.21/0.53      ((((k1_xboole_0)
% 0.21/0.53          = (k3_xboole_0 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1)))
% 0.21/0.53        | ~ (l1_struct_0 @ sk_C_1))),
% 0.21/0.53      inference('sup+', [status(thm)], ['1', '90'])).
% 0.21/0.53  thf('92', plain,
% 0.21/0.53      (((k3_xboole_0 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_C_1))
% 0.21/0.53         = (k2_struct_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.53  thf('93', plain, ((l1_struct_0 @ sk_C_1)),
% 0.21/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.53  thf('94', plain, (((k1_xboole_0) = (k2_struct_0 @ sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.21/0.53  thf('95', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((v2_struct_0 @ X0)
% 0.21/0.53          | ~ (l1_struct_0 @ X0)
% 0.21/0.53          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.21/0.53      inference('simplify', [status(thm)], ['71'])).
% 0.21/0.53  thf('96', plain,
% 0.21/0.53      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.53        | ~ (l1_struct_0 @ sk_B)
% 0.21/0.53        | (v2_struct_0 @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['94', '95'])).
% 0.21/0.53  thf('97', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.53  thf('98', plain, ((l1_struct_0 @ sk_B)),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf('99', plain, ((v2_struct_0 @ sk_B)),
% 0.21/0.53      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.21/0.53  thf('100', plain, ($false), inference('demod', [status(thm)], ['0', '99'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
