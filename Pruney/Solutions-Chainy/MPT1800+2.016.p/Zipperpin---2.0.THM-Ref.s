%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aMy0uTyraO

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:57 EST 2020

% Result     : Theorem 49.90s
% Output     : Refutation 49.90s
% Verified   : 
% Statistics : Number of formulae       :  222 ( 951 expanded)
%              Number of leaves         :   33 ( 267 expanded)
%              Depth                    :   24
%              Number of atoms          : 2526 (15068 expanded)
%              Number of equality atoms :  124 ( 614 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_tmap_1_type,type,(
    k6_tmap_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k8_tmap_1_type,type,(
    k8_tmap_1: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(t116_tmap_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ( ( ( v1_tsep_1 @ B @ A )
              & ( m1_pre_topc @ B @ A ) )
          <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
              = ( k8_tmap_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( m1_pre_topc @ B @ A ) )
           => ( ( ( v1_tsep_1 @ B @ A )
                & ( m1_pre_topc @ B @ A ) )
            <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                = ( k8_tmap_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t116_tmap_1])).

thf('0',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
   <= ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('7',plain,(
    ! [X24: $i] :
      ( ( m1_pre_topc @ X24 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X9 )
      | ~ ( m1_pre_topc @ X10 @ X9 )
      | ( m1_pre_topc @ X10 @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,
    ( ( ( m1_pre_topc @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( m1_pre_topc @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ( m1_pre_topc @ X7 @ X8 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( m1_pre_topc @ X0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_pre_topc @ X0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
        | ( m1_pre_topc @ X0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( m1_pre_topc @ sk_A @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf(t11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
            & ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) )).

thf('20',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X20 ) @ ( u1_pre_topc @ X20 ) ) @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('21',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('24',plain,
    ( ( m1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('25',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('26',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('30',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(d11_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( ( v1_pre_topc @ C )
                & ( v2_pre_topc @ C )
                & ( l1_pre_topc @ C ) )
             => ( ( C
                  = ( k8_tmap_1 @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( D
                        = ( u1_struct_0 @ B ) )
                     => ( C
                        = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( X13
       != ( k8_tmap_1 @ X12 @ X11 ) )
      | ( X14
       != ( u1_struct_0 @ X11 ) )
      | ( X13
        = ( k6_tmap_1 @ X12 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( v1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d11_tmap_1])).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ X12 @ X11 ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ X12 @ X11 ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ X12 @ X11 ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k8_tmap_1 @ X12 @ X11 )
        = ( k6_tmap_1 @ X12 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( m1_pre_topc @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( ( k8_tmap_1 @ sk_A @ sk_B )
        = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','40'])).

thf('42',plain,
    ( ( m1_pre_topc @ sk_A @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('43',plain,(
    ! [X24: $i] :
      ( ( m1_pre_topc @ X24 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('44',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X20 ) @ ( u1_pre_topc @ X20 ) ) @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('51',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t7_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ B )
             => ( m1_pre_topc @ C @ A ) ) ) ) )).

thf('55',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( m1_pre_topc @ X32 @ X31 )
      | ~ ( m1_pre_topc @ X32 @ X30 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t7_tsep_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( m1_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( m1_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( m1_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( m1_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( m1_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X1 @ X0 )
      | ( m1_pre_topc @ X1 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','60'])).

thf('62',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('63',plain,
    ( ( m1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('64',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('65',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('71',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( r1_tarski @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('78',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('79',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('80',plain,
    ( ( ~ ( r1_tarski @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( m1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('82',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X25 @ X26 )
      | ( r1_tarski @ ( u1_struct_0 @ X25 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('83',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['80','85'])).

thf('87',plain,
    ( ( m1_pre_topc @ sk_A @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','62','68','86'])).

thf('88',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X20 ) @ ( u1_pre_topc @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('89',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( u1_struct_0 @ ( k8_tmap_1 @ sk_A @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['80','85'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('92',plain,
    ( ( ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) )
      | ~ ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( l1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('94',plain,
    ( ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('96',plain,
    ( ( v1_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['89','94','95'])).

thf('97',plain,
    ( ( v2_pre_topc @ ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('98',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( k8_tmap_1 @ sk_A @ sk_B )
        = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['41','96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf(t106_tmap_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
              = ( k6_tmap_1 @ A @ B ) ) ) ) ) )).

thf('102',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X19 ) @ ( u1_pre_topc @ X19 ) )
       != ( k6_tmap_1 @ X19 @ X18 ) )
      | ( v3_pre_topc @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t106_tmap_1])).

thf('103',plain,
    ( ! [X0: $i] :
        ( ( ( k8_tmap_1 @ sk_A @ sk_B )
         != ( k6_tmap_1 @ sk_A @ X0 ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ! [X0: $i] :
        ( ( ( k8_tmap_1 @ sk_A @ sk_B )
         != ( k6_tmap_1 @ sk_A @ X0 ) )
        | ( v2_struct_0 @ sk_A )
        | ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,
    ( ( ( ( k8_tmap_1 @ sk_A @ sk_B )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['100','106'])).

thf('108',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('109',plain,
    ( ( ( ( k8_tmap_1 @ sk_A @ sk_B )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_tsep_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v3_pre_topc @ C @ A ) ) ) ) ) ) )).

thf('114',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ( ( sk_C @ X15 @ X16 )
        = ( u1_struct_0 @ X15 ) )
      | ( v1_tsep_1 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('115',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('119',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ~ ( v3_pre_topc @ ( sk_C @ X15 @ X16 ) @ X16 )
      | ( v1_tsep_1 @ X15 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('121',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
      | ( v1_tsep_1 @ sk_B @ sk_A ) )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('126',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ~ ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['112','126'])).

thf('128',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('129',plain,
    ( ( v1_tsep_1 @ sk_B @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['5'])).

thf('130',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('131',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X15 @ X16 )
      | ~ ( v1_tsep_1 @ X15 @ X16 )
      | ( X17
       != ( u1_struct_0 @ X15 ) )
      | ( v3_pre_topc @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_tsep_1])).

thf('132',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v3_pre_topc @ ( u1_struct_0 @ X15 ) @ X16 )
      | ~ ( v1_tsep_1 @ X15 @ X16 )
      | ~ ( m1_pre_topc @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,
    ( ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['130','132'])).

thf('134',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,
    ( ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['129','136'])).

thf('138',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('139',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X19 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X19 ) @ ( u1_pre_topc @ X19 ) )
        = ( k6_tmap_1 @ X19 @ X18 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t106_tmap_1])).

thf('140',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['140','141','142'])).

thf('144',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_B ) @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['137','145'])).

thf('147',plain,(
    ! [X24: $i] :
      ( ( m1_pre_topc @ X24 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('148',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X20 ) @ ( u1_pre_topc @ X20 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t11_tmap_1])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
    ( ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['146','150'])).

thf('152',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( ( sk_D @ X13 @ X11 @ X12 )
        = ( u1_struct_0 @ X11 ) )
      | ( X13
        = ( k8_tmap_1 @ X12 @ X11 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( v1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d11_tmap_1])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( X0
        = ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( ( sk_D @ X0 @ sk_B @ sk_A )
        = ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( X0
        = ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( ( sk_D @ X0 @ sk_B @ sk_A )
        = ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_pre_topc @ X11 @ X12 )
      | ( X13
       != ( k6_tmap_1 @ X12 @ ( sk_D @ X13 @ X11 @ X12 ) ) )
      | ( X13
        = ( k8_tmap_1 @ X12 @ X11 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( v1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d11_tmap_1])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      | ( X0
        = ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( X0
        = ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( m1_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( X0
       != ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      | ( X0
        = ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( X0
        = ( k8_tmap_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['161','162','163','164'])).

thf('166',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
    | ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,
    ( ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
        = ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['153','166'])).

thf('168',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['137','145'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('170',plain,
    ( ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['168','169'])).

thf('171',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( l1_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['137','145'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('175',plain,
    ( ( ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['173','174'])).

thf('176',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( v2_pre_topc @ ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['175','176','177'])).

thf('179',plain,
    ( ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
        = ( k8_tmap_1 @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['167','172','178'])).

thf('180',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['179','180'])).

thf('182',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) ) )
   <= ( v1_tsep_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['137','145'])).

thf('183',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('184',plain,
    ( ( ( k6_tmap_1 @ sk_A @ ( u1_struct_0 @ sk_B ) )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,
    ( ( ( k8_tmap_1 @ sk_A @ sk_B )
     != ( k8_tmap_1 @ sk_A @ sk_B ) )
   <= ( ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
       != ( k8_tmap_1 @ sk_A @ sk_B ) )
      & ( v1_tsep_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['181','184'])).

thf('186',plain,
    ( ~ ( v1_tsep_1 @ sk_B @ sk_A )
    | ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
      = ( k8_tmap_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','4','127','128','186'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aMy0uTyraO
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:25:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 49.90/50.09  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 49.90/50.09  % Solved by: fo/fo7.sh
% 49.90/50.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 49.90/50.09  % done 9978 iterations in 49.615s
% 49.90/50.09  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 49.90/50.09  % SZS output start Refutation
% 49.90/50.09  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 49.90/50.09  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 49.90/50.09  thf(sk_B_type, type, sk_B: $i).
% 49.90/50.09  thf(k6_tmap_1_type, type, k6_tmap_1: $i > $i > $i).
% 49.90/50.09  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 49.90/50.09  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 49.90/50.09  thf(k8_tmap_1_type, type, k8_tmap_1: $i > $i > $i).
% 49.90/50.09  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 49.90/50.09  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 49.90/50.09  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 49.90/50.09  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 49.90/50.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 49.90/50.09  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 49.90/50.09  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 49.90/50.09  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 49.90/50.09  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 49.90/50.09  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 49.90/50.09  thf(sk_A_type, type, sk_A: $i).
% 49.90/50.09  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 49.90/50.09  thf(t116_tmap_1, conjecture,
% 49.90/50.09    (![A:$i]:
% 49.90/50.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 49.90/50.09       ( ![B:$i]:
% 49.90/50.09         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 49.90/50.09           ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 49.90/50.09             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 49.90/50.09               ( k8_tmap_1 @ A @ B ) ) ) ) ) ))).
% 49.90/50.09  thf(zf_stmt_0, negated_conjecture,
% 49.90/50.09    (~( ![A:$i]:
% 49.90/50.09        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 49.90/50.09            ( l1_pre_topc @ A ) ) =>
% 49.90/50.09          ( ![B:$i]:
% 49.90/50.09            ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 49.90/50.09              ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) <=>
% 49.90/50.09                ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 49.90/50.09                  ( k8_tmap_1 @ A @ B ) ) ) ) ) ) )),
% 49.90/50.09    inference('cnf.neg', [status(esa)], [t116_tmap_1])).
% 49.90/50.09  thf('0', plain,
% 49.90/50.09      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09          != (k8_tmap_1 @ sk_A @ sk_B))
% 49.90/50.09        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 49.90/50.09        | ~ (v1_tsep_1 @ sk_B @ sk_A))),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('1', plain,
% 49.90/50.09      (~ ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 49.90/50.09       ~
% 49.90/50.09       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09          = (k8_tmap_1 @ sk_A @ sk_B))) | 
% 49.90/50.09       ~ ((m1_pre_topc @ sk_B @ sk_A))),
% 49.90/50.09      inference('split', [status(esa)], ['0'])).
% 49.90/50.09  thf('2', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('3', plain,
% 49.90/50.09      ((~ (m1_pre_topc @ sk_B @ sk_A)) <= (~ ((m1_pre_topc @ sk_B @ sk_A)))),
% 49.90/50.09      inference('split', [status(esa)], ['0'])).
% 49.90/50.09  thf('4', plain, (((m1_pre_topc @ sk_B @ sk_A))),
% 49.90/50.09      inference('sup-', [status(thm)], ['2', '3'])).
% 49.90/50.09  thf('5', plain,
% 49.90/50.09      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09          = (k8_tmap_1 @ sk_A @ sk_B))
% 49.90/50.09        | (v1_tsep_1 @ sk_B @ sk_A))),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('6', plain,
% 49.90/50.09      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09          = (k8_tmap_1 @ sk_A @ sk_B)))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('split', [status(esa)], ['5'])).
% 49.90/50.09  thf(t2_tsep_1, axiom,
% 49.90/50.09    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 49.90/50.09  thf('7', plain,
% 49.90/50.09      (![X24 : $i]: ((m1_pre_topc @ X24 @ X24) | ~ (l1_pre_topc @ X24))),
% 49.90/50.09      inference('cnf', [status(esa)], [t2_tsep_1])).
% 49.90/50.09  thf(t65_pre_topc, axiom,
% 49.90/50.09    (![A:$i]:
% 49.90/50.09     ( ( l1_pre_topc @ A ) =>
% 49.90/50.09       ( ![B:$i]:
% 49.90/50.09         ( ( l1_pre_topc @ B ) =>
% 49.90/50.09           ( ( m1_pre_topc @ A @ B ) <=>
% 49.90/50.09             ( m1_pre_topc @
% 49.90/50.09               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 49.90/50.09  thf('8', plain,
% 49.90/50.09      (![X9 : $i, X10 : $i]:
% 49.90/50.09         (~ (l1_pre_topc @ X9)
% 49.90/50.09          | ~ (m1_pre_topc @ X10 @ X9)
% 49.90/50.09          | (m1_pre_topc @ X10 @ 
% 49.90/50.09             (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 49.90/50.09          | ~ (l1_pre_topc @ X10))),
% 49.90/50.09      inference('cnf', [status(esa)], [t65_pre_topc])).
% 49.90/50.09  thf('9', plain,
% 49.90/50.09      (![X0 : $i]:
% 49.90/50.09         (~ (l1_pre_topc @ X0)
% 49.90/50.09          | ~ (l1_pre_topc @ X0)
% 49.90/50.09          | (m1_pre_topc @ X0 @ 
% 49.90/50.09             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 49.90/50.09          | ~ (l1_pre_topc @ X0))),
% 49.90/50.09      inference('sup-', [status(thm)], ['7', '8'])).
% 49.90/50.09  thf('10', plain,
% 49.90/50.09      (![X0 : $i]:
% 49.90/50.09         ((m1_pre_topc @ X0 @ 
% 49.90/50.09           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 49.90/50.09          | ~ (l1_pre_topc @ X0))),
% 49.90/50.09      inference('simplify', [status(thm)], ['9'])).
% 49.90/50.09  thf('11', plain,
% 49.90/50.09      ((((m1_pre_topc @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B))
% 49.90/50.09         | ~ (l1_pre_topc @ sk_A)))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('sup+', [status(thm)], ['6', '10'])).
% 49.90/50.09  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('13', plain,
% 49.90/50.09      (((m1_pre_topc @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B)))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('demod', [status(thm)], ['11', '12'])).
% 49.90/50.09  thf('14', plain,
% 49.90/50.09      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09          = (k8_tmap_1 @ sk_A @ sk_B)))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('split', [status(esa)], ['5'])).
% 49.90/50.09  thf(t59_pre_topc, axiom,
% 49.90/50.09    (![A:$i]:
% 49.90/50.09     ( ( l1_pre_topc @ A ) =>
% 49.90/50.09       ( ![B:$i]:
% 49.90/50.09         ( ( m1_pre_topc @
% 49.90/50.09             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 49.90/50.09           ( m1_pre_topc @ B @ A ) ) ) ))).
% 49.90/50.09  thf('15', plain,
% 49.90/50.09      (![X7 : $i, X8 : $i]:
% 49.90/50.09         (~ (m1_pre_topc @ X7 @ 
% 49.90/50.09             (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 49.90/50.09          | (m1_pre_topc @ X7 @ X8)
% 49.90/50.09          | ~ (l1_pre_topc @ X8))),
% 49.90/50.09      inference('cnf', [status(esa)], [t59_pre_topc])).
% 49.90/50.09  thf('16', plain,
% 49.90/50.09      ((![X0 : $i]:
% 49.90/50.09          (~ (m1_pre_topc @ X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 49.90/50.09           | ~ (l1_pre_topc @ sk_A)
% 49.90/50.09           | (m1_pre_topc @ X0 @ sk_A)))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('sup-', [status(thm)], ['14', '15'])).
% 49.90/50.09  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('18', plain,
% 49.90/50.09      ((![X0 : $i]:
% 49.90/50.09          (~ (m1_pre_topc @ X0 @ (k8_tmap_1 @ sk_A @ sk_B))
% 49.90/50.09           | (m1_pre_topc @ X0 @ sk_A)))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('demod', [status(thm)], ['16', '17'])).
% 49.90/50.09  thf('19', plain,
% 49.90/50.09      (((m1_pre_topc @ sk_A @ sk_A))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('sup-', [status(thm)], ['13', '18'])).
% 49.90/50.09  thf(t11_tmap_1, axiom,
% 49.90/50.09    (![A:$i]:
% 49.90/50.09     ( ( l1_pre_topc @ A ) =>
% 49.90/50.09       ( ![B:$i]:
% 49.90/50.09         ( ( m1_pre_topc @ B @ A ) =>
% 49.90/50.09           ( ( v1_pre_topc @
% 49.90/50.09               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 49.90/50.09             ( m1_pre_topc @
% 49.90/50.09               ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) @ A ) ) ) ) ))).
% 49.90/50.09  thf('20', plain,
% 49.90/50.09      (![X20 : $i, X21 : $i]:
% 49.90/50.09         (~ (m1_pre_topc @ X20 @ X21)
% 49.90/50.09          | (m1_pre_topc @ 
% 49.90/50.09             (g1_pre_topc @ (u1_struct_0 @ X20) @ (u1_pre_topc @ X20)) @ X21)
% 49.90/50.09          | ~ (l1_pre_topc @ X21))),
% 49.90/50.09      inference('cnf', [status(esa)], [t11_tmap_1])).
% 49.90/50.09  thf('21', plain,
% 49.90/50.09      (((~ (l1_pre_topc @ sk_A)
% 49.90/50.09         | (m1_pre_topc @ 
% 49.90/50.09            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_A)))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('sup-', [status(thm)], ['19', '20'])).
% 49.90/50.09  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('23', plain,
% 49.90/50.09      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09          = (k8_tmap_1 @ sk_A @ sk_B)))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('split', [status(esa)], ['5'])).
% 49.90/50.09  thf('24', plain,
% 49.90/50.09      (((m1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B) @ sk_A))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('demod', [status(thm)], ['21', '22', '23'])).
% 49.90/50.09  thf(dt_m1_pre_topc, axiom,
% 49.90/50.09    (![A:$i]:
% 49.90/50.09     ( ( l1_pre_topc @ A ) =>
% 49.90/50.09       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 49.90/50.09  thf('25', plain,
% 49.90/50.09      (![X5 : $i, X6 : $i]:
% 49.90/50.09         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 49.90/50.09      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 49.90/50.09  thf('26', plain,
% 49.90/50.09      (((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('sup-', [status(thm)], ['24', '25'])).
% 49.90/50.09  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('28', plain,
% 49.90/50.09      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('demod', [status(thm)], ['26', '27'])).
% 49.90/50.09  thf('29', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf(t1_tsep_1, axiom,
% 49.90/50.09    (![A:$i]:
% 49.90/50.09     ( ( l1_pre_topc @ A ) =>
% 49.90/50.09       ( ![B:$i]:
% 49.90/50.09         ( ( m1_pre_topc @ B @ A ) =>
% 49.90/50.09           ( m1_subset_1 @
% 49.90/50.09             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 49.90/50.09  thf('30', plain,
% 49.90/50.09      (![X22 : $i, X23 : $i]:
% 49.90/50.09         (~ (m1_pre_topc @ X22 @ X23)
% 49.90/50.09          | (m1_subset_1 @ (u1_struct_0 @ X22) @ 
% 49.90/50.09             (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 49.90/50.09          | ~ (l1_pre_topc @ X23))),
% 49.90/50.09      inference('cnf', [status(esa)], [t1_tsep_1])).
% 49.90/50.09  thf('31', plain,
% 49.90/50.09      ((~ (l1_pre_topc @ sk_A)
% 49.90/50.09        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 49.90/50.09           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 49.90/50.09      inference('sup-', [status(thm)], ['29', '30'])).
% 49.90/50.09  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('33', plain,
% 49.90/50.09      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 49.90/50.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 49.90/50.09      inference('demod', [status(thm)], ['31', '32'])).
% 49.90/50.09  thf(d11_tmap_1, axiom,
% 49.90/50.09    (![A:$i]:
% 49.90/50.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 49.90/50.09       ( ![B:$i]:
% 49.90/50.09         ( ( m1_pre_topc @ B @ A ) =>
% 49.90/50.09           ( ![C:$i]:
% 49.90/50.09             ( ( ( v1_pre_topc @ C ) & ( v2_pre_topc @ C ) & 
% 49.90/50.09                 ( l1_pre_topc @ C ) ) =>
% 49.90/50.09               ( ( ( C ) = ( k8_tmap_1 @ A @ B ) ) <=>
% 49.90/50.09                 ( ![D:$i]:
% 49.90/50.09                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 49.90/50.09                     ( ( ( D ) = ( u1_struct_0 @ B ) ) =>
% 49.90/50.09                       ( ( C ) = ( k6_tmap_1 @ A @ D ) ) ) ) ) ) ) ) ) ) ))).
% 49.90/50.09  thf('34', plain,
% 49.90/50.09      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 49.90/50.09         (~ (m1_pre_topc @ X11 @ X12)
% 49.90/50.09          | ((X13) != (k8_tmap_1 @ X12 @ X11))
% 49.90/50.09          | ((X14) != (u1_struct_0 @ X11))
% 49.90/50.09          | ((X13) = (k6_tmap_1 @ X12 @ X14))
% 49.90/50.09          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 49.90/50.09          | ~ (l1_pre_topc @ X13)
% 49.90/50.09          | ~ (v2_pre_topc @ X13)
% 49.90/50.09          | ~ (v1_pre_topc @ X13)
% 49.90/50.09          | ~ (l1_pre_topc @ X12)
% 49.90/50.09          | ~ (v2_pre_topc @ X12)
% 49.90/50.09          | (v2_struct_0 @ X12))),
% 49.90/50.09      inference('cnf', [status(esa)], [d11_tmap_1])).
% 49.90/50.09  thf('35', plain,
% 49.90/50.09      (![X11 : $i, X12 : $i]:
% 49.90/50.09         ((v2_struct_0 @ X12)
% 49.90/50.09          | ~ (v2_pre_topc @ X12)
% 49.90/50.09          | ~ (l1_pre_topc @ X12)
% 49.90/50.09          | ~ (v1_pre_topc @ (k8_tmap_1 @ X12 @ X11))
% 49.90/50.09          | ~ (v2_pre_topc @ (k8_tmap_1 @ X12 @ X11))
% 49.90/50.09          | ~ (l1_pre_topc @ (k8_tmap_1 @ X12 @ X11))
% 49.90/50.09          | ~ (m1_subset_1 @ (u1_struct_0 @ X11) @ 
% 49.90/50.09               (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 49.90/50.09          | ((k8_tmap_1 @ X12 @ X11) = (k6_tmap_1 @ X12 @ (u1_struct_0 @ X11)))
% 49.90/50.09          | ~ (m1_pre_topc @ X11 @ X12))),
% 49.90/50.09      inference('simplify', [status(thm)], ['34'])).
% 49.90/50.09  thf('36', plain,
% 49.90/50.09      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 49.90/50.09        | ((k8_tmap_1 @ sk_A @ sk_B)
% 49.90/50.09            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 49.90/50.09        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 49.90/50.09        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 49.90/50.09        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 49.90/50.09        | ~ (l1_pre_topc @ sk_A)
% 49.90/50.09        | ~ (v2_pre_topc @ sk_A)
% 49.90/50.09        | (v2_struct_0 @ sk_A))),
% 49.90/50.09      inference('sup-', [status(thm)], ['33', '35'])).
% 49.90/50.09  thf('37', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('40', plain,
% 49.90/50.09      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 49.90/50.09        | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 49.90/50.09        | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 49.90/50.09        | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 49.90/50.09        | (v2_struct_0 @ sk_A))),
% 49.90/50.09      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 49.90/50.09  thf('41', plain,
% 49.90/50.09      ((((v2_struct_0 @ sk_A)
% 49.90/50.09         | ~ (v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 49.90/50.09         | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 49.90/50.09         | ((k8_tmap_1 @ sk_A @ sk_B)
% 49.90/50.09             = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('sup-', [status(thm)], ['28', '40'])).
% 49.90/50.09  thf('42', plain,
% 49.90/50.09      (((m1_pre_topc @ sk_A @ (k8_tmap_1 @ sk_A @ sk_B)))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('demod', [status(thm)], ['11', '12'])).
% 49.90/50.09  thf('43', plain,
% 49.90/50.09      (![X24 : $i]: ((m1_pre_topc @ X24 @ X24) | ~ (l1_pre_topc @ X24))),
% 49.90/50.09      inference('cnf', [status(esa)], [t2_tsep_1])).
% 49.90/50.09  thf('44', plain,
% 49.90/50.09      (![X20 : $i, X21 : $i]:
% 49.90/50.09         (~ (m1_pre_topc @ X20 @ X21)
% 49.90/50.09          | (m1_pre_topc @ 
% 49.90/50.09             (g1_pre_topc @ (u1_struct_0 @ X20) @ (u1_pre_topc @ X20)) @ X21)
% 49.90/50.09          | ~ (l1_pre_topc @ X21))),
% 49.90/50.09      inference('cnf', [status(esa)], [t11_tmap_1])).
% 49.90/50.09  thf('45', plain,
% 49.90/50.09      (![X0 : $i]:
% 49.90/50.09         (~ (l1_pre_topc @ X0)
% 49.90/50.09          | ~ (l1_pre_topc @ X0)
% 49.90/50.09          | (m1_pre_topc @ 
% 49.90/50.09             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0))),
% 49.90/50.09      inference('sup-', [status(thm)], ['43', '44'])).
% 49.90/50.09  thf('46', plain,
% 49.90/50.09      (![X0 : $i]:
% 49.90/50.09         ((m1_pre_topc @ 
% 49.90/50.09           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 49.90/50.09          | ~ (l1_pre_topc @ X0))),
% 49.90/50.09      inference('simplify', [status(thm)], ['45'])).
% 49.90/50.09  thf('47', plain,
% 49.90/50.09      (![X5 : $i, X6 : $i]:
% 49.90/50.09         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 49.90/50.09      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 49.90/50.09  thf('48', plain,
% 49.90/50.09      (![X0 : $i]:
% 49.90/50.09         (~ (l1_pre_topc @ X0)
% 49.90/50.09          | ~ (l1_pre_topc @ X0)
% 49.90/50.09          | (l1_pre_topc @ 
% 49.90/50.09             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 49.90/50.09      inference('sup-', [status(thm)], ['46', '47'])).
% 49.90/50.09  thf('49', plain,
% 49.90/50.09      (![X0 : $i]:
% 49.90/50.09         ((l1_pre_topc @ 
% 49.90/50.09           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 49.90/50.09          | ~ (l1_pre_topc @ X0))),
% 49.90/50.09      inference('simplify', [status(thm)], ['48'])).
% 49.90/50.09  thf('50', plain,
% 49.90/50.09      (![X0 : $i]:
% 49.90/50.09         ((m1_pre_topc @ 
% 49.90/50.09           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ X0)
% 49.90/50.09          | ~ (l1_pre_topc @ X0))),
% 49.90/50.09      inference('simplify', [status(thm)], ['45'])).
% 49.90/50.09  thf(cc1_pre_topc, axiom,
% 49.90/50.09    (![A:$i]:
% 49.90/50.09     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 49.90/50.09       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 49.90/50.09  thf('51', plain,
% 49.90/50.09      (![X3 : $i, X4 : $i]:
% 49.90/50.09         (~ (m1_pre_topc @ X3 @ X4)
% 49.90/50.09          | (v2_pre_topc @ X3)
% 49.90/50.09          | ~ (l1_pre_topc @ X4)
% 49.90/50.09          | ~ (v2_pre_topc @ X4))),
% 49.90/50.09      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 49.90/50.09  thf('52', plain,
% 49.90/50.09      (![X0 : $i]:
% 49.90/50.09         (~ (l1_pre_topc @ X0)
% 49.90/50.09          | ~ (v2_pre_topc @ X0)
% 49.90/50.09          | ~ (l1_pre_topc @ X0)
% 49.90/50.09          | (v2_pre_topc @ 
% 49.90/50.09             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 49.90/50.09      inference('sup-', [status(thm)], ['50', '51'])).
% 49.90/50.09  thf('53', plain,
% 49.90/50.09      (![X0 : $i]:
% 49.90/50.09         ((v2_pre_topc @ 
% 49.90/50.09           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 49.90/50.09          | ~ (v2_pre_topc @ X0)
% 49.90/50.09          | ~ (l1_pre_topc @ X0))),
% 49.90/50.09      inference('simplify', [status(thm)], ['52'])).
% 49.90/50.09  thf('54', plain,
% 49.90/50.09      (![X0 : $i]:
% 49.90/50.09         ((m1_pre_topc @ X0 @ 
% 49.90/50.09           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 49.90/50.09          | ~ (l1_pre_topc @ X0))),
% 49.90/50.09      inference('simplify', [status(thm)], ['9'])).
% 49.90/50.09  thf(t7_tsep_1, axiom,
% 49.90/50.09    (![A:$i]:
% 49.90/50.09     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 49.90/50.09       ( ![B:$i]:
% 49.90/50.09         ( ( m1_pre_topc @ B @ A ) =>
% 49.90/50.09           ( ![C:$i]: ( ( m1_pre_topc @ C @ B ) => ( m1_pre_topc @ C @ A ) ) ) ) ) ))).
% 49.90/50.09  thf('55', plain,
% 49.90/50.09      (![X30 : $i, X31 : $i, X32 : $i]:
% 49.90/50.09         (~ (m1_pre_topc @ X30 @ X31)
% 49.90/50.09          | (m1_pre_topc @ X32 @ X31)
% 49.90/50.09          | ~ (m1_pre_topc @ X32 @ X30)
% 49.90/50.09          | ~ (l1_pre_topc @ X31)
% 49.90/50.09          | ~ (v2_pre_topc @ X31))),
% 49.90/50.09      inference('cnf', [status(esa)], [t7_tsep_1])).
% 49.90/50.09  thf('56', plain,
% 49.90/50.09      (![X0 : $i, X1 : $i]:
% 49.90/50.09         (~ (l1_pre_topc @ X0)
% 49.90/50.09          | ~ (v2_pre_topc @ 
% 49.90/50.09               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 49.90/50.09          | ~ (l1_pre_topc @ 
% 49.90/50.09               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 49.90/50.09          | ~ (m1_pre_topc @ X1 @ X0)
% 49.90/50.09          | (m1_pre_topc @ X1 @ 
% 49.90/50.09             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 49.90/50.09      inference('sup-', [status(thm)], ['54', '55'])).
% 49.90/50.09  thf('57', plain,
% 49.90/50.09      (![X0 : $i, X1 : $i]:
% 49.90/50.09         (~ (l1_pre_topc @ X0)
% 49.90/50.09          | ~ (v2_pre_topc @ X0)
% 49.90/50.09          | (m1_pre_topc @ X1 @ 
% 49.90/50.09             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 49.90/50.09          | ~ (m1_pre_topc @ X1 @ X0)
% 49.90/50.09          | ~ (l1_pre_topc @ 
% 49.90/50.09               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 49.90/50.09          | ~ (l1_pre_topc @ X0))),
% 49.90/50.09      inference('sup-', [status(thm)], ['53', '56'])).
% 49.90/50.09  thf('58', plain,
% 49.90/50.09      (![X0 : $i, X1 : $i]:
% 49.90/50.09         (~ (l1_pre_topc @ 
% 49.90/50.09             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 49.90/50.09          | ~ (m1_pre_topc @ X1 @ X0)
% 49.90/50.09          | (m1_pre_topc @ X1 @ 
% 49.90/50.09             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 49.90/50.09          | ~ (v2_pre_topc @ X0)
% 49.90/50.09          | ~ (l1_pre_topc @ X0))),
% 49.90/50.09      inference('simplify', [status(thm)], ['57'])).
% 49.90/50.09  thf('59', plain,
% 49.90/50.09      (![X0 : $i, X1 : $i]:
% 49.90/50.09         (~ (l1_pre_topc @ X0)
% 49.90/50.09          | ~ (l1_pre_topc @ X0)
% 49.90/50.09          | ~ (v2_pre_topc @ X0)
% 49.90/50.09          | (m1_pre_topc @ X1 @ 
% 49.90/50.09             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 49.90/50.09          | ~ (m1_pre_topc @ X1 @ X0))),
% 49.90/50.09      inference('sup-', [status(thm)], ['49', '58'])).
% 49.90/50.09  thf('60', plain,
% 49.90/50.09      (![X0 : $i, X1 : $i]:
% 49.90/50.09         (~ (m1_pre_topc @ X1 @ X0)
% 49.90/50.09          | (m1_pre_topc @ X1 @ 
% 49.90/50.09             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 49.90/50.09          | ~ (v2_pre_topc @ X0)
% 49.90/50.09          | ~ (l1_pre_topc @ X0))),
% 49.90/50.09      inference('simplify', [status(thm)], ['59'])).
% 49.90/50.09  thf('61', plain,
% 49.90/50.09      (((~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 49.90/50.09         | ~ (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 49.90/50.09         | (m1_pre_topc @ sk_A @ 
% 49.90/50.09            (g1_pre_topc @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ 
% 49.90/50.09             (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('sup-', [status(thm)], ['42', '60'])).
% 49.90/50.09  thf('62', plain,
% 49.90/50.09      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('demod', [status(thm)], ['26', '27'])).
% 49.90/50.09  thf('63', plain,
% 49.90/50.09      (((m1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B) @ sk_A))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('demod', [status(thm)], ['21', '22', '23'])).
% 49.90/50.09  thf('64', plain,
% 49.90/50.09      (![X3 : $i, X4 : $i]:
% 49.90/50.09         (~ (m1_pre_topc @ X3 @ X4)
% 49.90/50.09          | (v2_pre_topc @ X3)
% 49.90/50.09          | ~ (l1_pre_topc @ X4)
% 49.90/50.09          | ~ (v2_pre_topc @ X4))),
% 49.90/50.09      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 49.90/50.09  thf('65', plain,
% 49.90/50.09      (((~ (v2_pre_topc @ sk_A)
% 49.90/50.09         | ~ (l1_pre_topc @ sk_A)
% 49.90/50.09         | (v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('sup-', [status(thm)], ['63', '64'])).
% 49.90/50.09  thf('66', plain, ((v2_pre_topc @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('68', plain,
% 49.90/50.09      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('demod', [status(thm)], ['65', '66', '67'])).
% 49.90/50.09  thf('69', plain,
% 49.90/50.09      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09          = (k8_tmap_1 @ sk_A @ sk_B)))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('split', [status(esa)], ['5'])).
% 49.90/50.09  thf('70', plain,
% 49.90/50.09      (![X0 : $i]:
% 49.90/50.09         ((m1_pre_topc @ X0 @ 
% 49.90/50.09           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 49.90/50.09          | ~ (l1_pre_topc @ X0))),
% 49.90/50.09      inference('simplify', [status(thm)], ['9'])).
% 49.90/50.09  thf(t35_borsuk_1, axiom,
% 49.90/50.09    (![A:$i]:
% 49.90/50.09     ( ( l1_pre_topc @ A ) =>
% 49.90/50.09       ( ![B:$i]:
% 49.90/50.09         ( ( m1_pre_topc @ B @ A ) =>
% 49.90/50.09           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 49.90/50.09  thf('71', plain,
% 49.90/50.09      (![X25 : $i, X26 : $i]:
% 49.90/50.09         (~ (m1_pre_topc @ X25 @ X26)
% 49.90/50.09          | (r1_tarski @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X26))
% 49.90/50.09          | ~ (l1_pre_topc @ X26))),
% 49.90/50.09      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 49.90/50.09  thf('72', plain,
% 49.90/50.09      (![X0 : $i]:
% 49.90/50.09         (~ (l1_pre_topc @ X0)
% 49.90/50.09          | ~ (l1_pre_topc @ 
% 49.90/50.09               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 49.90/50.09          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 49.90/50.09             (u1_struct_0 @ 
% 49.90/50.09              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))))),
% 49.90/50.09      inference('sup-', [status(thm)], ['70', '71'])).
% 49.90/50.09  thf('73', plain,
% 49.90/50.09      (((~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 49.90/50.09         | (r1_tarski @ (u1_struct_0 @ sk_A) @ 
% 49.90/50.09            (u1_struct_0 @ 
% 49.90/50.09             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 49.90/50.09         | ~ (l1_pre_topc @ sk_A)))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('sup-', [status(thm)], ['69', '72'])).
% 49.90/50.09  thf('74', plain,
% 49.90/50.09      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09          = (k8_tmap_1 @ sk_A @ sk_B)))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('split', [status(esa)], ['5'])).
% 49.90/50.09  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('76', plain,
% 49.90/50.09      (((~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))
% 49.90/50.09         | (r1_tarski @ (u1_struct_0 @ sk_A) @ 
% 49.90/50.09            (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('demod', [status(thm)], ['73', '74', '75'])).
% 49.90/50.09  thf('77', plain,
% 49.90/50.09      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('demod', [status(thm)], ['26', '27'])).
% 49.90/50.09  thf('78', plain,
% 49.90/50.09      (((r1_tarski @ (u1_struct_0 @ sk_A) @ 
% 49.90/50.09         (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B))))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('demod', [status(thm)], ['76', '77'])).
% 49.90/50.09  thf(d10_xboole_0, axiom,
% 49.90/50.09    (![A:$i,B:$i]:
% 49.90/50.09     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 49.90/50.09  thf('79', plain,
% 49.90/50.09      (![X0 : $i, X2 : $i]:
% 49.90/50.09         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 49.90/50.09      inference('cnf', [status(esa)], [d10_xboole_0])).
% 49.90/50.09  thf('80', plain,
% 49.90/50.09      (((~ (r1_tarski @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ 
% 49.90/50.09            (u1_struct_0 @ sk_A))
% 49.90/50.09         | ((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A))))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('sup-', [status(thm)], ['78', '79'])).
% 49.90/50.09  thf('81', plain,
% 49.90/50.09      (((m1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B) @ sk_A))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('demod', [status(thm)], ['21', '22', '23'])).
% 49.90/50.09  thf('82', plain,
% 49.90/50.09      (![X25 : $i, X26 : $i]:
% 49.90/50.09         (~ (m1_pre_topc @ X25 @ X26)
% 49.90/50.09          | (r1_tarski @ (u1_struct_0 @ X25) @ (u1_struct_0 @ X26))
% 49.90/50.09          | ~ (l1_pre_topc @ X26))),
% 49.90/50.09      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 49.90/50.09  thf('83', plain,
% 49.90/50.09      (((~ (l1_pre_topc @ sk_A)
% 49.90/50.09         | (r1_tarski @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ 
% 49.90/50.09            (u1_struct_0 @ sk_A))))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('sup-', [status(thm)], ['81', '82'])).
% 49.90/50.09  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('85', plain,
% 49.90/50.09      (((r1_tarski @ (u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) @ 
% 49.90/50.09         (u1_struct_0 @ sk_A)))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('demod', [status(thm)], ['83', '84'])).
% 49.90/50.09  thf('86', plain,
% 49.90/50.09      ((((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('demod', [status(thm)], ['80', '85'])).
% 49.90/50.09  thf('87', plain,
% 49.90/50.09      (((m1_pre_topc @ sk_A @ 
% 49.90/50.09         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 49.90/50.09          (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('demod', [status(thm)], ['61', '62', '68', '86'])).
% 49.90/50.09  thf('88', plain,
% 49.90/50.09      (![X20 : $i, X21 : $i]:
% 49.90/50.09         (~ (m1_pre_topc @ X20 @ X21)
% 49.90/50.09          | (v1_pre_topc @ 
% 49.90/50.09             (g1_pre_topc @ (u1_struct_0 @ X20) @ (u1_pre_topc @ X20)))
% 49.90/50.09          | ~ (l1_pre_topc @ X21))),
% 49.90/50.09      inference('cnf', [status(esa)], [t11_tmap_1])).
% 49.90/50.09  thf('89', plain,
% 49.90/50.09      (((~ (l1_pre_topc @ 
% 49.90/50.09            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 49.90/50.09             (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))
% 49.90/50.09         | (v1_pre_topc @ 
% 49.90/50.09            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('sup-', [status(thm)], ['87', '88'])).
% 49.90/50.09  thf('90', plain,
% 49.90/50.09      ((((u1_struct_0 @ (k8_tmap_1 @ sk_A @ sk_B)) = (u1_struct_0 @ sk_A)))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('demod', [status(thm)], ['80', '85'])).
% 49.90/50.09  thf('91', plain,
% 49.90/50.09      (![X0 : $i]:
% 49.90/50.09         ((l1_pre_topc @ 
% 49.90/50.09           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 49.90/50.09          | ~ (l1_pre_topc @ X0))),
% 49.90/50.09      inference('simplify', [status(thm)], ['48'])).
% 49.90/50.09  thf('92', plain,
% 49.90/50.09      ((((l1_pre_topc @ 
% 49.90/50.09          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 49.90/50.09           (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))
% 49.90/50.09         | ~ (l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B))))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('sup+', [status(thm)], ['90', '91'])).
% 49.90/50.09  thf('93', plain,
% 49.90/50.09      (((l1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('demod', [status(thm)], ['26', '27'])).
% 49.90/50.09  thf('94', plain,
% 49.90/50.09      (((l1_pre_topc @ 
% 49.90/50.09         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ 
% 49.90/50.09          (u1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('demod', [status(thm)], ['92', '93'])).
% 49.90/50.09  thf('95', plain,
% 49.90/50.09      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09          = (k8_tmap_1 @ sk_A @ sk_B)))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('split', [status(esa)], ['5'])).
% 49.90/50.09  thf('96', plain,
% 49.90/50.09      (((v1_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('demod', [status(thm)], ['89', '94', '95'])).
% 49.90/50.09  thf('97', plain,
% 49.90/50.09      (((v2_pre_topc @ (k8_tmap_1 @ sk_A @ sk_B)))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('demod', [status(thm)], ['65', '66', '67'])).
% 49.90/50.09  thf('98', plain,
% 49.90/50.09      ((((v2_struct_0 @ sk_A)
% 49.90/50.09         | ((k8_tmap_1 @ sk_A @ sk_B)
% 49.90/50.09             = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('demod', [status(thm)], ['41', '96', '97'])).
% 49.90/50.09  thf('99', plain, (~ (v2_struct_0 @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('100', plain,
% 49.90/50.09      ((((k8_tmap_1 @ sk_A @ sk_B) = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('clc', [status(thm)], ['98', '99'])).
% 49.90/50.09  thf('101', plain,
% 49.90/50.09      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09          = (k8_tmap_1 @ sk_A @ sk_B)))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('split', [status(esa)], ['5'])).
% 49.90/50.09  thf(t106_tmap_1, axiom,
% 49.90/50.09    (![A:$i]:
% 49.90/50.09     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 49.90/50.09       ( ![B:$i]:
% 49.90/50.09         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 49.90/50.09           ( ( v3_pre_topc @ B @ A ) <=>
% 49.90/50.09             ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 49.90/50.09               ( k6_tmap_1 @ A @ B ) ) ) ) ) ))).
% 49.90/50.09  thf('102', plain,
% 49.90/50.09      (![X18 : $i, X19 : $i]:
% 49.90/50.09         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 49.90/50.09          | ((g1_pre_topc @ (u1_struct_0 @ X19) @ (u1_pre_topc @ X19))
% 49.90/50.09              != (k6_tmap_1 @ X19 @ X18))
% 49.90/50.09          | (v3_pre_topc @ X18 @ X19)
% 49.90/50.09          | ~ (l1_pre_topc @ X19)
% 49.90/50.09          | ~ (v2_pre_topc @ X19)
% 49.90/50.09          | (v2_struct_0 @ X19))),
% 49.90/50.09      inference('cnf', [status(esa)], [t106_tmap_1])).
% 49.90/50.09  thf('103', plain,
% 49.90/50.09      ((![X0 : $i]:
% 49.90/50.09          (((k8_tmap_1 @ sk_A @ sk_B) != (k6_tmap_1 @ sk_A @ X0))
% 49.90/50.09           | (v2_struct_0 @ sk_A)
% 49.90/50.09           | ~ (v2_pre_topc @ sk_A)
% 49.90/50.09           | ~ (l1_pre_topc @ sk_A)
% 49.90/50.09           | (v3_pre_topc @ X0 @ sk_A)
% 49.90/50.09           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('sup-', [status(thm)], ['101', '102'])).
% 49.90/50.09  thf('104', plain, ((v2_pre_topc @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('106', plain,
% 49.90/50.09      ((![X0 : $i]:
% 49.90/50.09          (((k8_tmap_1 @ sk_A @ sk_B) != (k6_tmap_1 @ sk_A @ X0))
% 49.90/50.09           | (v2_struct_0 @ sk_A)
% 49.90/50.09           | (v3_pre_topc @ X0 @ sk_A)
% 49.90/50.09           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('demod', [status(thm)], ['103', '104', '105'])).
% 49.90/50.09  thf('107', plain,
% 49.90/50.09      (((((k8_tmap_1 @ sk_A @ sk_B) != (k8_tmap_1 @ sk_A @ sk_B))
% 49.90/50.09         | ~ (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 49.90/50.09              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 49.90/50.09         | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 49.90/50.09         | (v2_struct_0 @ sk_A)))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('sup-', [status(thm)], ['100', '106'])).
% 49.90/50.09  thf('108', plain,
% 49.90/50.09      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 49.90/50.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 49.90/50.09      inference('demod', [status(thm)], ['31', '32'])).
% 49.90/50.09  thf('109', plain,
% 49.90/50.09      (((((k8_tmap_1 @ sk_A @ sk_B) != (k8_tmap_1 @ sk_A @ sk_B))
% 49.90/50.09         | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 49.90/50.09         | (v2_struct_0 @ sk_A)))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('demod', [status(thm)], ['107', '108'])).
% 49.90/50.09  thf('110', plain,
% 49.90/50.09      ((((v2_struct_0 @ sk_A) | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('simplify', [status(thm)], ['109'])).
% 49.90/50.09  thf('111', plain, (~ (v2_struct_0 @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('112', plain,
% 49.90/50.09      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 49.90/50.09         <= ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('clc', [status(thm)], ['110', '111'])).
% 49.90/50.09  thf('113', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf(d1_tsep_1, axiom,
% 49.90/50.09    (![A:$i]:
% 49.90/50.09     ( ( l1_pre_topc @ A ) =>
% 49.90/50.09       ( ![B:$i]:
% 49.90/50.09         ( ( m1_pre_topc @ B @ A ) =>
% 49.90/50.09           ( ( v1_tsep_1 @ B @ A ) <=>
% 49.90/50.09             ( ![C:$i]:
% 49.90/50.09               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 49.90/50.09                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ))).
% 49.90/50.09  thf('114', plain,
% 49.90/50.09      (![X15 : $i, X16 : $i]:
% 49.90/50.09         (~ (m1_pre_topc @ X15 @ X16)
% 49.90/50.09          | ((sk_C @ X15 @ X16) = (u1_struct_0 @ X15))
% 49.90/50.09          | (v1_tsep_1 @ X15 @ X16)
% 49.90/50.09          | ~ (l1_pre_topc @ X16))),
% 49.90/50.09      inference('cnf', [status(esa)], [d1_tsep_1])).
% 49.90/50.09  thf('115', plain,
% 49.90/50.09      ((~ (l1_pre_topc @ sk_A)
% 49.90/50.09        | (v1_tsep_1 @ sk_B @ sk_A)
% 49.90/50.09        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 49.90/50.09      inference('sup-', [status(thm)], ['113', '114'])).
% 49.90/50.09  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('117', plain,
% 49.90/50.09      (((v1_tsep_1 @ sk_B @ sk_A)
% 49.90/50.09        | ((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 49.90/50.09      inference('demod', [status(thm)], ['115', '116'])).
% 49.90/50.09  thf('118', plain,
% 49.90/50.09      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 49.90/50.09      inference('split', [status(esa)], ['0'])).
% 49.90/50.09  thf('119', plain,
% 49.90/50.09      ((((sk_C @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))
% 49.90/50.09         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 49.90/50.09      inference('sup-', [status(thm)], ['117', '118'])).
% 49.90/50.09  thf('120', plain,
% 49.90/50.09      (![X15 : $i, X16 : $i]:
% 49.90/50.09         (~ (m1_pre_topc @ X15 @ X16)
% 49.90/50.09          | ~ (v3_pre_topc @ (sk_C @ X15 @ X16) @ X16)
% 49.90/50.09          | (v1_tsep_1 @ X15 @ X16)
% 49.90/50.09          | ~ (l1_pre_topc @ X16))),
% 49.90/50.09      inference('cnf', [status(esa)], [d1_tsep_1])).
% 49.90/50.09  thf('121', plain,
% 49.90/50.09      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 49.90/50.09         | ~ (l1_pre_topc @ sk_A)
% 49.90/50.09         | (v1_tsep_1 @ sk_B @ sk_A)
% 49.90/50.09         | ~ (m1_pre_topc @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 49.90/50.09      inference('sup-', [status(thm)], ['119', '120'])).
% 49.90/50.09  thf('122', plain, ((l1_pre_topc @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('123', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('124', plain,
% 49.90/50.09      (((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 49.90/50.09         | (v1_tsep_1 @ sk_B @ sk_A))) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 49.90/50.09      inference('demod', [status(thm)], ['121', '122', '123'])).
% 49.90/50.09  thf('125', plain,
% 49.90/50.09      ((~ (v1_tsep_1 @ sk_B @ sk_A)) <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 49.90/50.09      inference('split', [status(esa)], ['0'])).
% 49.90/50.09  thf('126', plain,
% 49.90/50.09      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 49.90/50.09         <= (~ ((v1_tsep_1 @ sk_B @ sk_A)))),
% 49.90/50.09      inference('clc', [status(thm)], ['124', '125'])).
% 49.90/50.09  thf('127', plain,
% 49.90/50.09      (((v1_tsep_1 @ sk_B @ sk_A)) | 
% 49.90/50.09       ~
% 49.90/50.09       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09          = (k8_tmap_1 @ sk_A @ sk_B)))),
% 49.90/50.09      inference('sup-', [status(thm)], ['112', '126'])).
% 49.90/50.09  thf('128', plain,
% 49.90/50.09      (((v1_tsep_1 @ sk_B @ sk_A)) | 
% 49.90/50.09       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09          = (k8_tmap_1 @ sk_A @ sk_B)))),
% 49.90/50.09      inference('split', [status(esa)], ['5'])).
% 49.90/50.09  thf('129', plain,
% 49.90/50.09      (((v1_tsep_1 @ sk_B @ sk_A)) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 49.90/50.09      inference('split', [status(esa)], ['5'])).
% 49.90/50.09  thf('130', plain,
% 49.90/50.09      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 49.90/50.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 49.90/50.09      inference('demod', [status(thm)], ['31', '32'])).
% 49.90/50.09  thf('131', plain,
% 49.90/50.09      (![X15 : $i, X16 : $i, X17 : $i]:
% 49.90/50.09         (~ (m1_pre_topc @ X15 @ X16)
% 49.90/50.09          | ~ (v1_tsep_1 @ X15 @ X16)
% 49.90/50.09          | ((X17) != (u1_struct_0 @ X15))
% 49.90/50.09          | (v3_pre_topc @ X17 @ X16)
% 49.90/50.09          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 49.90/50.09          | ~ (l1_pre_topc @ X16))),
% 49.90/50.09      inference('cnf', [status(esa)], [d1_tsep_1])).
% 49.90/50.09  thf('132', plain,
% 49.90/50.09      (![X15 : $i, X16 : $i]:
% 49.90/50.09         (~ (l1_pre_topc @ X16)
% 49.90/50.09          | ~ (m1_subset_1 @ (u1_struct_0 @ X15) @ 
% 49.90/50.09               (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 49.90/50.09          | (v3_pre_topc @ (u1_struct_0 @ X15) @ X16)
% 49.90/50.09          | ~ (v1_tsep_1 @ X15 @ X16)
% 49.90/50.09          | ~ (m1_pre_topc @ X15 @ X16))),
% 49.90/50.09      inference('simplify', [status(thm)], ['131'])).
% 49.90/50.09  thf('133', plain,
% 49.90/50.09      ((~ (m1_pre_topc @ sk_B @ sk_A)
% 49.90/50.09        | ~ (v1_tsep_1 @ sk_B @ sk_A)
% 49.90/50.09        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 49.90/50.09        | ~ (l1_pre_topc @ sk_A))),
% 49.90/50.09      inference('sup-', [status(thm)], ['130', '132'])).
% 49.90/50.09  thf('134', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('135', plain, ((l1_pre_topc @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('136', plain,
% 49.90/50.09      ((~ (v1_tsep_1 @ sk_B @ sk_A)
% 49.90/50.09        | (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 49.90/50.09      inference('demod', [status(thm)], ['133', '134', '135'])).
% 49.90/50.09  thf('137', plain,
% 49.90/50.09      (((v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))
% 49.90/50.09         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 49.90/50.09      inference('sup-', [status(thm)], ['129', '136'])).
% 49.90/50.09  thf('138', plain,
% 49.90/50.09      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 49.90/50.09        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 49.90/50.09      inference('demod', [status(thm)], ['31', '32'])).
% 49.90/50.09  thf('139', plain,
% 49.90/50.09      (![X18 : $i, X19 : $i]:
% 49.90/50.09         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 49.90/50.09          | ~ (v3_pre_topc @ X18 @ X19)
% 49.90/50.09          | ((g1_pre_topc @ (u1_struct_0 @ X19) @ (u1_pre_topc @ X19))
% 49.90/50.09              = (k6_tmap_1 @ X19 @ X18))
% 49.90/50.09          | ~ (l1_pre_topc @ X19)
% 49.90/50.09          | ~ (v2_pre_topc @ X19)
% 49.90/50.09          | (v2_struct_0 @ X19))),
% 49.90/50.09      inference('cnf', [status(esa)], [t106_tmap_1])).
% 49.90/50.09  thf('140', plain,
% 49.90/50.09      (((v2_struct_0 @ sk_A)
% 49.90/50.09        | ~ (v2_pre_topc @ sk_A)
% 49.90/50.09        | ~ (l1_pre_topc @ sk_A)
% 49.90/50.09        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 49.90/50.09        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 49.90/50.09      inference('sup-', [status(thm)], ['138', '139'])).
% 49.90/50.09  thf('141', plain, ((v2_pre_topc @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('142', plain, ((l1_pre_topc @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('143', plain,
% 49.90/50.09      (((v2_struct_0 @ sk_A)
% 49.90/50.09        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 49.90/50.09        | ~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A))),
% 49.90/50.09      inference('demod', [status(thm)], ['140', '141', '142'])).
% 49.90/50.09  thf('144', plain, (~ (v2_struct_0 @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('145', plain,
% 49.90/50.09      ((~ (v3_pre_topc @ (u1_struct_0 @ sk_B) @ sk_A)
% 49.90/50.09        | ((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09            = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))),
% 49.90/50.09      inference('clc', [status(thm)], ['143', '144'])).
% 49.90/50.09  thf('146', plain,
% 49.90/50.09      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09          = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 49.90/50.09         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 49.90/50.09      inference('sup-', [status(thm)], ['137', '145'])).
% 49.90/50.09  thf('147', plain,
% 49.90/50.09      (![X24 : $i]: ((m1_pre_topc @ X24 @ X24) | ~ (l1_pre_topc @ X24))),
% 49.90/50.09      inference('cnf', [status(esa)], [t2_tsep_1])).
% 49.90/50.09  thf('148', plain,
% 49.90/50.09      (![X20 : $i, X21 : $i]:
% 49.90/50.09         (~ (m1_pre_topc @ X20 @ X21)
% 49.90/50.09          | (v1_pre_topc @ 
% 49.90/50.09             (g1_pre_topc @ (u1_struct_0 @ X20) @ (u1_pre_topc @ X20)))
% 49.90/50.09          | ~ (l1_pre_topc @ X21))),
% 49.90/50.09      inference('cnf', [status(esa)], [t11_tmap_1])).
% 49.90/50.09  thf('149', plain,
% 49.90/50.09      (![X0 : $i]:
% 49.90/50.09         (~ (l1_pre_topc @ X0)
% 49.90/50.09          | ~ (l1_pre_topc @ X0)
% 49.90/50.09          | (v1_pre_topc @ 
% 49.90/50.09             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 49.90/50.09      inference('sup-', [status(thm)], ['147', '148'])).
% 49.90/50.09  thf('150', plain,
% 49.90/50.09      (![X0 : $i]:
% 49.90/50.09         ((v1_pre_topc @ 
% 49.90/50.09           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 49.90/50.09          | ~ (l1_pre_topc @ X0))),
% 49.90/50.09      inference('simplify', [status(thm)], ['149'])).
% 49.90/50.09  thf('151', plain,
% 49.90/50.09      ((((v1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 49.90/50.09         | ~ (l1_pre_topc @ sk_A))) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 49.90/50.09      inference('sup+', [status(thm)], ['146', '150'])).
% 49.90/50.09  thf('152', plain, ((l1_pre_topc @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('153', plain,
% 49.90/50.09      (((v1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 49.90/50.09         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 49.90/50.09      inference('demod', [status(thm)], ['151', '152'])).
% 49.90/50.09  thf('154', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('155', plain,
% 49.90/50.09      (![X11 : $i, X12 : $i, X13 : $i]:
% 49.90/50.09         (~ (m1_pre_topc @ X11 @ X12)
% 49.90/50.09          | ((sk_D @ X13 @ X11 @ X12) = (u1_struct_0 @ X11))
% 49.90/50.09          | ((X13) = (k8_tmap_1 @ X12 @ X11))
% 49.90/50.09          | ~ (l1_pre_topc @ X13)
% 49.90/50.09          | ~ (v2_pre_topc @ X13)
% 49.90/50.09          | ~ (v1_pre_topc @ X13)
% 49.90/50.09          | ~ (l1_pre_topc @ X12)
% 49.90/50.09          | ~ (v2_pre_topc @ X12)
% 49.90/50.09          | (v2_struct_0 @ X12))),
% 49.90/50.09      inference('cnf', [status(esa)], [d11_tmap_1])).
% 49.90/50.09  thf('156', plain,
% 49.90/50.09      (![X0 : $i]:
% 49.90/50.09         ((v2_struct_0 @ sk_A)
% 49.90/50.09          | ~ (v2_pre_topc @ sk_A)
% 49.90/50.09          | ~ (l1_pre_topc @ sk_A)
% 49.90/50.09          | ~ (v1_pre_topc @ X0)
% 49.90/50.09          | ~ (v2_pre_topc @ X0)
% 49.90/50.09          | ~ (l1_pre_topc @ X0)
% 49.90/50.09          | ((X0) = (k8_tmap_1 @ sk_A @ sk_B))
% 49.90/50.09          | ((sk_D @ X0 @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 49.90/50.09      inference('sup-', [status(thm)], ['154', '155'])).
% 49.90/50.09  thf('157', plain, ((v2_pre_topc @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('158', plain, ((l1_pre_topc @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('159', plain,
% 49.90/50.09      (![X0 : $i]:
% 49.90/50.09         ((v2_struct_0 @ sk_A)
% 49.90/50.09          | ~ (v1_pre_topc @ X0)
% 49.90/50.09          | ~ (v2_pre_topc @ X0)
% 49.90/50.09          | ~ (l1_pre_topc @ X0)
% 49.90/50.09          | ((X0) = (k8_tmap_1 @ sk_A @ sk_B))
% 49.90/50.09          | ((sk_D @ X0 @ sk_B @ sk_A) = (u1_struct_0 @ sk_B)))),
% 49.90/50.09      inference('demod', [status(thm)], ['156', '157', '158'])).
% 49.90/50.09  thf('160', plain,
% 49.90/50.09      (![X11 : $i, X12 : $i, X13 : $i]:
% 49.90/50.09         (~ (m1_pre_topc @ X11 @ X12)
% 49.90/50.09          | ((X13) != (k6_tmap_1 @ X12 @ (sk_D @ X13 @ X11 @ X12)))
% 49.90/50.09          | ((X13) = (k8_tmap_1 @ X12 @ X11))
% 49.90/50.09          | ~ (l1_pre_topc @ X13)
% 49.90/50.09          | ~ (v2_pre_topc @ X13)
% 49.90/50.09          | ~ (v1_pre_topc @ X13)
% 49.90/50.09          | ~ (l1_pre_topc @ X12)
% 49.90/50.09          | ~ (v2_pre_topc @ X12)
% 49.90/50.09          | (v2_struct_0 @ X12))),
% 49.90/50.09      inference('cnf', [status(esa)], [d11_tmap_1])).
% 49.90/50.09  thf('161', plain,
% 49.90/50.09      (![X0 : $i]:
% 49.90/50.09         (((X0) != (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 49.90/50.09          | ((X0) = (k8_tmap_1 @ sk_A @ sk_B))
% 49.90/50.09          | ~ (l1_pre_topc @ X0)
% 49.90/50.09          | ~ (v2_pre_topc @ X0)
% 49.90/50.09          | ~ (v1_pre_topc @ X0)
% 49.90/50.09          | (v2_struct_0 @ sk_A)
% 49.90/50.09          | (v2_struct_0 @ sk_A)
% 49.90/50.09          | ~ (v2_pre_topc @ sk_A)
% 49.90/50.09          | ~ (l1_pre_topc @ sk_A)
% 49.90/50.09          | ~ (v1_pre_topc @ X0)
% 49.90/50.09          | ~ (v2_pre_topc @ X0)
% 49.90/50.09          | ~ (l1_pre_topc @ X0)
% 49.90/50.09          | ((X0) = (k8_tmap_1 @ sk_A @ sk_B))
% 49.90/50.09          | ~ (m1_pre_topc @ sk_B @ sk_A))),
% 49.90/50.09      inference('sup-', [status(thm)], ['159', '160'])).
% 49.90/50.09  thf('162', plain, ((v2_pre_topc @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('163', plain, ((l1_pre_topc @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('164', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('165', plain,
% 49.90/50.09      (![X0 : $i]:
% 49.90/50.09         (((X0) != (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 49.90/50.09          | ((X0) = (k8_tmap_1 @ sk_A @ sk_B))
% 49.90/50.09          | ~ (l1_pre_topc @ X0)
% 49.90/50.09          | ~ (v2_pre_topc @ X0)
% 49.90/50.09          | ~ (v1_pre_topc @ X0)
% 49.90/50.09          | (v2_struct_0 @ sk_A)
% 49.90/50.09          | (v2_struct_0 @ sk_A)
% 49.90/50.09          | ~ (v1_pre_topc @ X0)
% 49.90/50.09          | ~ (v2_pre_topc @ X0)
% 49.90/50.09          | ~ (l1_pre_topc @ X0)
% 49.90/50.09          | ((X0) = (k8_tmap_1 @ sk_A @ sk_B)))),
% 49.90/50.09      inference('demod', [status(thm)], ['161', '162', '163', '164'])).
% 49.90/50.09  thf('166', plain,
% 49.90/50.09      (((v2_struct_0 @ sk_A)
% 49.90/50.09        | ~ (v1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 49.90/50.09        | ~ (v2_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 49.90/50.09        | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 49.90/50.09        | ((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))
% 49.90/50.09            = (k8_tmap_1 @ sk_A @ sk_B)))),
% 49.90/50.09      inference('simplify', [status(thm)], ['165'])).
% 49.90/50.09  thf('167', plain,
% 49.90/50.09      (((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) = (k8_tmap_1 @ sk_A @ sk_B))
% 49.90/50.09         | ~ (l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 49.90/50.09         | ~ (v2_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 49.90/50.09         | (v2_struct_0 @ sk_A))) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 49.90/50.09      inference('sup-', [status(thm)], ['153', '166'])).
% 49.90/50.09  thf('168', plain,
% 49.90/50.09      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09          = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 49.90/50.09         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 49.90/50.09      inference('sup-', [status(thm)], ['137', '145'])).
% 49.90/50.09  thf('169', plain,
% 49.90/50.09      (![X0 : $i]:
% 49.90/50.09         ((l1_pre_topc @ 
% 49.90/50.09           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 49.90/50.09          | ~ (l1_pre_topc @ X0))),
% 49.90/50.09      inference('simplify', [status(thm)], ['48'])).
% 49.90/50.09  thf('170', plain,
% 49.90/50.09      ((((l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 49.90/50.09         | ~ (l1_pre_topc @ sk_A))) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 49.90/50.09      inference('sup+', [status(thm)], ['168', '169'])).
% 49.90/50.09  thf('171', plain, ((l1_pre_topc @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('172', plain,
% 49.90/50.09      (((l1_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 49.90/50.09         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 49.90/50.09      inference('demod', [status(thm)], ['170', '171'])).
% 49.90/50.09  thf('173', plain,
% 49.90/50.09      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09          = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 49.90/50.09         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 49.90/50.09      inference('sup-', [status(thm)], ['137', '145'])).
% 49.90/50.09  thf('174', plain,
% 49.90/50.09      (![X0 : $i]:
% 49.90/50.09         ((v2_pre_topc @ 
% 49.90/50.09           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 49.90/50.09          | ~ (v2_pre_topc @ X0)
% 49.90/50.09          | ~ (l1_pre_topc @ X0))),
% 49.90/50.09      inference('simplify', [status(thm)], ['52'])).
% 49.90/50.09  thf('175', plain,
% 49.90/50.09      ((((v2_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)))
% 49.90/50.09         | ~ (l1_pre_topc @ sk_A)
% 49.90/50.09         | ~ (v2_pre_topc @ sk_A))) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 49.90/50.09      inference('sup+', [status(thm)], ['173', '174'])).
% 49.90/50.09  thf('176', plain, ((l1_pre_topc @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('177', plain, ((v2_pre_topc @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('178', plain,
% 49.90/50.09      (((v2_pre_topc @ (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 49.90/50.09         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 49.90/50.09      inference('demod', [status(thm)], ['175', '176', '177'])).
% 49.90/50.09  thf('179', plain,
% 49.90/50.09      (((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) = (k8_tmap_1 @ sk_A @ sk_B))
% 49.90/50.09         | (v2_struct_0 @ sk_A))) <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 49.90/50.09      inference('demod', [status(thm)], ['167', '172', '178'])).
% 49.90/50.09  thf('180', plain, (~ (v2_struct_0 @ sk_A)),
% 49.90/50.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 49.90/50.09  thf('181', plain,
% 49.90/50.09      ((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) = (k8_tmap_1 @ sk_A @ sk_B)))
% 49.90/50.09         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 49.90/50.09      inference('clc', [status(thm)], ['179', '180'])).
% 49.90/50.09  thf('182', plain,
% 49.90/50.09      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09          = (k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B))))
% 49.90/50.09         <= (((v1_tsep_1 @ sk_B @ sk_A)))),
% 49.90/50.09      inference('sup-', [status(thm)], ['137', '145'])).
% 49.90/50.09  thf('183', plain,
% 49.90/50.09      ((((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09          != (k8_tmap_1 @ sk_A @ sk_B)))
% 49.90/50.09         <= (~
% 49.90/50.09             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))))),
% 49.90/50.09      inference('split', [status(esa)], ['0'])).
% 49.90/50.09  thf('184', plain,
% 49.90/50.09      ((((k6_tmap_1 @ sk_A @ (u1_struct_0 @ sk_B)) != (k8_tmap_1 @ sk_A @ sk_B)))
% 49.90/50.09         <= (~
% 49.90/50.09             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))) & 
% 49.90/50.09             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 49.90/50.09      inference('sup-', [status(thm)], ['182', '183'])).
% 49.90/50.09  thf('185', plain,
% 49.90/50.09      ((((k8_tmap_1 @ sk_A @ sk_B) != (k8_tmap_1 @ sk_A @ sk_B)))
% 49.90/50.09         <= (~
% 49.90/50.09             (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09                = (k8_tmap_1 @ sk_A @ sk_B))) & 
% 49.90/50.09             ((v1_tsep_1 @ sk_B @ sk_A)))),
% 49.90/50.09      inference('sup-', [status(thm)], ['181', '184'])).
% 49.90/50.09  thf('186', plain,
% 49.90/50.09      (~ ((v1_tsep_1 @ sk_B @ sk_A)) | 
% 49.90/50.09       (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 49.90/50.09          = (k8_tmap_1 @ sk_A @ sk_B)))),
% 49.90/50.09      inference('simplify', [status(thm)], ['185'])).
% 49.90/50.09  thf('187', plain, ($false),
% 49.90/50.09      inference('sat_resolution*', [status(thm)],
% 49.90/50.09                ['1', '4', '127', '128', '186'])).
% 49.90/50.09  
% 49.90/50.09  % SZS output end Refutation
% 49.90/50.09  
% 49.92/50.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
